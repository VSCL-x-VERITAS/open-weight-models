#!/usr/bin/env python3
"""Drive native Codex app-server with fresh trials and observable continuations."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import queue
import subprocess
import threading
import time
import traceback

from observe import summary

class Driver:
    def __init__(self, case):
        self.case = case
        self.launch = json.loads((case / 'launch.json').read_text())
        self.observer = case / 'observer'
        self.observer.mkdir(exist_ok=True)
        self.lock = (self.observer / 'driver.lock').open('a')
        try:
            fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError('This case already has an active native driver; refusing duplicate model work')
        self.raw = (self.observer / 'app-server-private.jsonl').open('a', buffering=1)
        os.chmod(self.raw.name, 0o600)
        env = {**os.environ, **self.launch['env']}
        # Native authentication, never a model-visible API key or proxy credential.
        for key in ('OPENAI_API_KEY', 'OPENAI_BASE_URL', 'OPENROUTER_API_KEY', 'ANTHROPIC_API_KEY'):
            env.pop(key, None)
        err = (self.observer / 'app-server-stderr.log').open('a')
        self.process = subprocess.Popen([self.launch['codex'], 'app-server', '--stdio'],
            cwd=self.launch['workspace'], env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=err, text=True, bufsize=1)
        self.incoming = queue.Queue()
        self.number = 0
        self.deferred = []
        self.thread_id = None
        self.active_turns = set()
        self.last_metrics_refresh = 0
        self.record('process_started', pid=self.process.pid)
        threading.Thread(target=self.reader, daemon=True).start()

    def record(self, kind, **fields):
        with (self.observer / 'lifecycle.jsonl').open('a') as f:
            f.write(json.dumps({'unix': time.time(), 'type': kind, **fields}) + '\n')

    def save_metrics(self, force=False):
        if not force and time.monotonic() - self.last_metrics_refresh < 5:
            return
        self.last_metrics_refresh = time.monotonic()
        try:
            data = summary(self.case)
            dest = self.observer / 'measurement-summary.json'
            temp = dest.with_suffix('.tmp')
            temp.write_text(json.dumps(data, indent=2) + '\n')
            temp.replace(dest)
        except Exception as e:
            self.record('measurement_error', error=type(e).__name__)

    def reader(self):
        for line in self.process.stdout:
            try:
                message = json.loads(line)
            except ValueError:
                continue
            self.raw.write(json.dumps({'unix': time.time(), 'message': message}) + '\n')
            self.incoming.put(message)
        self.incoming.put({'process_eof': self.process.poll()})

    def send(self, message):
        self.process.stdin.write(json.dumps(message) + '\n')
        self.process.stdin.flush()

    def notification(self, message):
        method = message.get('method', '')
        params = message.get('params') or {}
        if 'id' in message and method:
            # Never elevate outside the frozen permissions profile or fabricate
            # user answers. Unexpected client requests become explicit blockers.
            self.record('client_request_blocked', method=method)
            self.send({'id': message['id'], 'error': {'code': -32000, 'message': 'Unattended clean trial: no elevation or fabricated user input.'}})
        if method == 'turn/started':
            turn = params.get('turn', {})
            tid = turn.get('id')
            if tid and tid not in self.active_turns:
                self.active_turns.add(tid)
                self.record('turn_started', turn_id=tid, thread_id=params.get('threadId'))
        elif method == 'turn/completed':
            turn = params.get('turn', {})
            tid = turn.get('id')
            if tid in self.active_turns:
                self.active_turns.remove(tid)
                self.record('turn_completed' if turn.get('status') == 'completed' else 'turn_failed',
                            turn_id=tid, thread_id=params.get('threadId'), status=turn.get('status'), error=turn.get('error'))
        elif method == 'error':
            self.record('native_error', error=params)
        self.save_metrics()

    def rpc(self, method, params):
        self.number += 1
        request_id = self.number
        self.send({'id': request_id, 'method': method, 'params': params})
        while True:
            message = self.get_message()
            if message.get('id') == request_id and 'method' not in message:
                if 'error' in message:
                    raise RuntimeError(f'{method}: {message["error"]}')
                return message.get('result')
            self.notification(message)
            self.deferred.append(message)

    def get_message(self):
        while True:
            try:
                message = self.incoming.get(timeout=10)
            except queue.Empty:
                self.save_metrics()
                if self.process.poll() is not None:
                    raise RuntimeError('Native app-server exited')
                continue
            if 'process_eof' in message:
                raise RuntimeError('Native app-server stdout closed')
            return message

    def turn(self, text):
        result = self.rpc('turn/start', {'threadId': self.thread_id,
            'input': [{'type': 'text', 'text': text}], 'model': 'gpt-6.1-sol', 'effort': 'high',
            'approvalPolicy': 'never', 'permissions': 'clean-trial'})
        tid = result['turn']['id']
        if tid not in self.active_turns:
            self.active_turns.add(tid)
            self.record('turn_started', turn_id=tid, thread_id=self.thread_id)
        pending = self.deferred
        self.deferred = []
        while True:
            message = pending.pop(0) if pending else self.get_message()
            self.notification(message)
            params = message.get('params') or {}
            if message.get('method') == 'turn/completed' and params.get('threadId') == self.thread_id and params.get('turn', {}).get('id') == tid:
                if params['turn'].get('status') != 'completed':
                    raise RuntimeError(f'Turn ended {params["turn"].get("status")}')
                return

    def run(self, resume=False, resume_prompt='run/RESUME_AFTER_OPERATOR_001.txt'):
        self.rpc('initialize', {'clientInfo': {'name': 'hdp-clean-trial', 'version': '1.0.0'}, 'capabilities': {'experimentalApi': True}})
        self.send({'method': 'initialized'})
        work = Path(self.launch['workspace'])
        if resume:
            events = [json.loads(s) for s in (self.observer / 'lifecycle.jsonl').read_text().splitlines()]
            roots = [r['thread_id'] for r in events if r['type'] == 'thread_created']
            if len(set(roots)) != 1:
                raise RuntimeError('Resume requires one unambiguous existing root thread')
            original_thread = roots[0]
            restored = self.rpc('thread/resume', {'threadId': original_thread, 'excludeTurns': True,
                'cwd': self.launch['workspace'], 'model': 'gpt-6.1-sol', 'modelProvider': 'openai',
                'approvalPolicy': 'never', 'permissions': 'clean-trial'})
            self.thread_id = restored['thread']['id']
            if self.thread_id != original_thread:
                raise RuntimeError('Resume changed the original thread identity')
            prompt_path = work / resume_prompt
            self.record('assisted_resume', thread_id=self.thread_id, intervention_id='operator-clarification-001',
                prompt_path=resume_prompt, prompt_sha256=hashlib.sha256(prompt_path.read_bytes()).hexdigest())
            self.record('state', state='assisted_formalization_running')
            self.turn(prompt_path.read_text())
        else:
            start = self.rpc('thread/start', {'cwd': self.launch['workspace'], 'model': 'gpt-6.1-sol',
                    'modelProvider': 'openai', 'approvalPolicy': 'never', 'permissions': 'clean-trial',
                    'ephemeral': False, 'allowProviderModelFallback': False})
            self.thread_id = start['thread']['id']
            self.record('thread_created', thread_id=self.thread_id)
            self.record('state', state='setup_running')
            self.turn((work / 'run/SETUP_PROMPT.txt').read_text())
            if not (work / 'reports/SETUP_READY.json').exists():
                raise RuntimeError('Setup ended without SETUP_READY.json; inspect native output before mathematical work')
            ready = json.loads((work / 'reports/SETUP_READY.json').read_text())
            if ready.get('ready') is not True:
                raise RuntimeError('Setup explicitly reported not ready')
            with (work / 'reports/phase-events.jsonl').open('a') as f:
                f.write(json.dumps({'unix': time.time(), 'phase': 'formalization', 'source': 'observer, after setup turn completion'}) + '\n')
            self.record('state', state='formalization_running')
            self.turn((work / 'run/START_PROMPT.txt').read_text())
        while True:
            status_file = work / 'reports/STATUS.json'
            status = json.loads(status_file.read_text()) if status_file.exists() else {}
            if status.get('state') in ('claimed_complete_pending_audit', 'blocked'):
                self.record('state', state=status['state'])
                break
            self.record('automatic_continuation', reason='Normal turn stopped without recorded completion or typed blocker; no mathematical hints added.')
            self.turn((work / 'run/CONTINUE_PROMPT.txt').read_text())
        self.save_metrics(force=True)

    def close(self):
        for tid in list(self.active_turns):
            self.record('turn_interrupted', turn_id=tid, reason='observer shutdown')
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
        self.save_metrics(force=True)
        self.lock.close()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--resume', action='store_true', help='Continue the same persisted native root thread; never rerun setup or reset proofs')
    parser.add_argument('--resume-prompt', default='run/RESUME_AFTER_OPERATOR_001.txt')
    parser.add_argument('cases', nargs='+', type=Path)
    args = parser.parse_args()
    for case in args.cases:
        driver = None
        try:
            driver = Driver(case.resolve())
            driver.run(resume=args.resume, resume_prompt=args.resume_prompt)
        except Exception as error:
            if driver:
                driver.record('state', state='observer_or_native_failure', error=str(error))
                (driver.observer / 'failure.txt').write_text(traceback.format_exc())
            return 1
        finally:
            if driver:
                driver.close()
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
