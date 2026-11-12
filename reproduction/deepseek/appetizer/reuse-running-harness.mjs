import { execFileSync } from 'node:child_process';
import { readFileSync, realpathSync } from 'node:fs';
import { join } from 'node:path';

const [experimentDir, ...args] = process.argv.slice(2);
let port = 3086;
for (let i = 0; i < args.length; i++) {
  if (args[i] === '--port') port = Number(args[++i]);
  else if (args[i].startsWith('--port=')) port = Number(args[i].slice(7));
}
if (!Number.isInteger(port) || port < 0 || port > 65535) {
  console.error('The port must be an integer between 0 and 65535.');
  process.exit(1);
}
// Port 0 explicitly asks the harness to choose an unused port.
if (port === 0) process.exit(10);

function lsof(args) {
  try {
    return execFileSync('/usr/sbin/lsof', args, {
      encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], timeout: 5000,
    });
  } catch (error) {
    // lsof returns 1 when no matching process/file exists.
    if (error.status === 1 && !String(error.stderr ?? '').trim()) return '';
    throw error;
  }
}

try {
  const pids = [...new Set(lsof([
    '-nP', `-iTCP@127.0.0.1:${port}`, '-sTCP:LISTEN', '-t',
  ]).trim().split(/\s+/).filter(Boolean))];
  if (!pids.length) process.exit(10);

  const workspace = realpathSync(join(experimentDir, 'workspace'));
  for (const pid of pids) {
    const cwd = lsof(['-a', '-p', pid, '-d', 'cwd', '-Fn'])
      .split('\n').find(line => line.startsWith('n'))?.slice(1);
    if (cwd !== workspace) continue;

    // Require both our workspace and the harness's actual startup receipt.
    const log = readFileSync(join(experimentDir, 'logs/server.log'), 'utf8');
    const urls = [...log.matchAll(/^dsh web: (http:\/\/127\.0\.0\.1:\d+\/\?token=\S+)$/gm)];
    const url = urls.at(-1)?.[1];
    if (!url || Number(new URL(url).port) !== port) continue;
    const response = await fetch(url, { redirect: 'manual', signal: AbortSignal.timeout(3000) });
    if (response.status >= 400) continue;
    console.log(`DeepSeek Harness is already running (PID ${pid}). Reusing it.`);
    console.log(`dsh web: ${url}`);
    console.log('Open the URL above. No second server was started.');
    process.exit(0);
  }
  console.error(`Port ${port} is occupied, but I could not verify it as this experiment's running harness.`);
  console.error('No process was stopped. Check the existing listener before starting another server.');
  process.exit(1);
} catch (error) {
  console.error(`Could not check the existing harness: ${error.message}`);
  process.exit(1);
}
