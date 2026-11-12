import errno, json, socket
from pathlib import Path
forbidden = {'prior_product': '/Users/gspyrou/Documents/ChatGPT/George S/output/hdp-deepseek-formalization/appetizer/HDP.lean', 'prior_attempt': '/Users/gspyrou/Documents/ChatGPT/George S/output/deepseek-appetizer-clean-api/workspace/lean/HDP.lean', 'prior_audit': '/Users/gspyrou/Documents/ChatGPT/George S/output/hdp-independent-correspondence-audit/audit.json', 'other_new_case': '/Users/gspyrou/Documents/ChatGPT/George S/output/codex-hdp-clean/chapter01/workspace/lean/HDP.lean', 'global_credentials': '/Users/gspyrou/.codex/auth.json', 'native_credentials': '/Users/gspyrou/Documents/ChatGPT/George S/.tools/codex-hdp-operator/trials/appetizer/codex-home/auth.json', 'skill_book_package': '/Users/gspyrou/Documents/ChatGPT/George S/.tools/codex-hdp-operator/workflow-latest/books/vershynin-hdp/book.json', 'root_repository': '/Users/gspyrou/Documents/ChatGPT/George S/.git/config'}
results = []
for label, path in forbidden.items():
    try:
        with Path(path).open('rb') as stream:
            stream.read(1)
    except PermissionError:
        results.append({'check': label, 'denied': True})
    except OSError as error:
        results.append({'check': label, 'denied': error.errno in (errno.EPERM, errno.EACCES), 'errno': error.errno})
    else:
        results.append({'check': label, 'denied': False})
sock = socket.socket()
sock.settimeout(2)
try:
    sock.connect(('127.0.0.1', 3084))
except OSError as error:
    results.append({'check': 'other_harness_network', 'denied': error.errno in (errno.EPERM, errno.EACCES), 'errno': error.errno})
else:
    results.append({'check': 'other_harness_network', 'denied': False})
finally:
    sock.close()
assert Path('source/Appetizer.pdf').read_bytes().startswith(b'%PDF')
assert Path('lean/.lake/packages/mathlib/Mathlib.lean').is_file()
assert Path('lean/HDP.lean').read_text() == 'import Mathlib\n'
print(json.dumps({'checks': results, 'positive_source_and_mathlib': True}))
assert all(item['denied'] for item in results), 'ISOLATION FAILED: do not begin formalization'
