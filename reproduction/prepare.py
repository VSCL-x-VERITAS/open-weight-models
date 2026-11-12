#!/usr/bin/env python3
"""Prepare a fresh PDF-only trial. No model requests are made."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import stat
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = "/Users/gspyrou/Documents/ChatGPT/George S"
OLD_NODE = "/Users/gspyrou/.nvm/versions/node/v24.19.0"
WORKFLOW = "1fb46504020649465d98ef2533a926e8c1e4dbf4"
SKILLS = ("book-formalization", "book-formalization-migration",
          "formalization-faithfulness-audit", "formalization-code-review")


def run(*args, cwd=None, env=None):
    subprocess.run(args, cwd=cwd, env=env, check=True)


def dump(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def seed(model, case, pdf, work):
    source_spec = ROOT / "reproduction/deepseek" / case / "experiment.json"
    spec = json.loads(source_spec.read_text())
    if hashlib.sha256(pdf.read_bytes()).hexdigest() != spec["source_sha256"]:
        raise ValueError(f"PDF SHA-256 mismatch for {case}. See SOURCE.md in results/deepseek.")
    product = ROOT / "results" / model / case
    for part in ("source", "lean", "run", "reports", "tools"):
        (work / part).mkdir(parents=True, exist_ok=True)
    shutil.copyfile(pdf, work / spec["source_pdf"])
    for filename in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        shutil.copyfile(product / filename, work / "lean" / filename)
    (work / "lean/HDP.lean").write_text("import Mathlib\n")
    if model == "deepseek":
        protocol = ROOT / "results/deepseek/provenance" / case
        shutil.copyfile(protocol / "AGENTS.md", work / "AGENTS.md")
        shutil.copytree(protocol / "run", work / "run", dirs_exist_ok=True)
        shutil.copyfile(source_spec, work / "run/experiment.json")
    else:
        protocol = product / "experiment"
        shutil.copyfile(protocol / "AGENTS.md", work / "AGENTS.md")
        for prompt in protocol.glob("*PROMPT.txt"):
            shutil.copyfile(prompt, work / "run" / prompt.name)
    return spec


def cache(work, elan):
    env = dict(os.environ, ELAN_HOME=str(elan))
    lake = str(elan / "bin/lake")
    lean = work / "lean"
    run(lake, "exe", "cache", "get", cwd=lean, env=env)
    for pkg in json.loads((lean / "lake-manifest.json").read_text())["packages"]:
        checkout = lean / ".lake/packages" / pkg["name"]
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
        changes = subprocess.check_output(["git", "status", "--porcelain"], cwd=checkout, text=True)
        if actual != pkg["rev"] or changes:
            raise ValueError(f"Dependency verification failed: {pkg['name']}")
    run(lake, "build", "HDP", cwd=lean, env=env)


def preflight_script(work, forbidden, pdf):
    (work / "tools/isolation_check.py").write_text(
        'import errno, json, socket\nfrom pathlib import Path\n'
        f'forbidden = {forbidden!r}\n'
        'for name, path in forbidden.items():\n'
        '    try:\n        with Path(path).open("rb") as stream:\n            stream.read(1)\n'
        '    except OSError as error:\n        assert error.errno in (errno.EACCES, errno.EPERM), (name, error.errno)\n'
        '    else:\n        raise RuntimeError("Readable forbidden input: " + name)\n'
        'with socket.socket() as sock:\n'
        '    sock.settimeout(2)\n'
        '    try:\n        sock.connect(("127.0.0.1", 1))\n'
        '    except OSError as error:\n        assert error.errno in (errno.EACCES, errno.EPERM), error.errno\n'
        '    else:\n        raise RuntimeError("Unexpected tool network access")\n'
        f'assert Path({pdf!r}).read_bytes().startswith(b"%PDF")\n'
        'assert Path("lean/.lake/packages/mathlib/Mathlib.lean").is_file()\n'
        'assert Path("lean/HDP.lean").read_text() == "import Mathlib\\n"\n'
        'print(json.dumps({"checks": [{"check": n, "denied": True} for n in forbidden], "positive_source_and_mathlib": True}))\n')


def prepare_codex(args, base, work, spec):
    workflow, auth, codex = args.workflow, args.auth, args.codex
    head = subprocess.check_output(["git", "-C", workflow, "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", workflow, "status", "--porcelain"], text=True)
    if head != WORKFLOW or dirty:
        raise ValueError("Use a clean checkout of the exact pinned workflow commit.")
    if not auth.is_file() or not codex.is_file():
        raise ValueError("Provide a native Codex binary and existing file-backed ChatGPT sign-in.")
    home = base / "codex-home"
    (home / "skills").mkdir(parents=True)
    for skill in SKILLS:
        package = workflow / "skills" / skill
        if not (package / "SKILL.md").is_file():
            raise ValueError(f"Missing skill: {package}")
        (home / "skills" / skill).symlink_to(package, target_is_directory=True)
    (home / "auth.json").symlink_to(auth)
    if args.models_cache:
        shutil.copyfile(args.models_cache, home / "models_cache.json")
    tmp = base / "tmp"
    tmp.mkdir()
    (base / "observer").mkdir()
    run("git", "init", "-q", "-b", "codex/clean-trial", work)
    forbidden = {
        "released_product": str(ROOT / "results/deepseek/appetizer/HDP.lean"),
        "repository_metadata": str(work / ".git/config"),
        "native_credentials": str(home / "auth.json"),
        "global_credentials": str(auth),
        "skill_book_package": str(next((workflow / "books/vershynin-hdp").rglob("*.json"))),
    }
    preflight_script(work, forbidden, spec["source_pdf"])
    agents = work / "AGENTS.md"
    agents.write_text(re.sub(r"at /[^\n]+/skills/book-formalization/SKILL\.md",
                             lambda _: f"at {home}/skills/book-formalization/SKILL.md",
                             agents.read_text(), count=1))
    env = {
        "PATH": f"{args.elan}/bin:{args.tool_bin}:/usr/bin:/bin:/usr/sbin:/sbin",
        "ELAN_HOME": str(args.elan), "CODEX_HOME": str(home), "TMPDIR": str(tmp),
        "PYTHONNOUSERSITE": "1", "PYTHONDONTWRITEBYTECODE": "1",
    }
    fs = {":root": "deny", ":minimal": "read", ":tmpdir": "deny", ":slash_tmp": "deny",
          str(work): "write", str(tmp): "write"}
    for path in (args.tool_bin.parent, codex.parent, args.elan, workflow / "skills",
                 workflow / "project-development/current", home / "skills"):
        fs[str(path)] = "read"
    for path in ("AGENTS.md", "run", "source", "tools", "lean/lean-toolchain",
                 "lean/lake-manifest.json", "lean/.lake/packages"):
        fs[str(work / path)] = "read"
    fs[str(work / ".git")] = "deny"
    fs[str(workflow / "skills/**/tests/**")] = "deny"
    for denied in (ROOT, auth, home / "auth.json", home / "sessions",
                   workflow / "books", workflow / "transcripts"):
        fs[str(denied)] = "deny"
    lines = ['model = "gpt-6.1-sol"', 'model_reasoning_effort = "high"',
             'model_provider = "openai"', 'approval_policy = "never"',
             'default_permissions = "clean-trial"', 'web_search = "disabled"',
             'project_doc_max_bytes = 0', 'cli_auth_credentials_store = "file"',
             '[features]', 'apps = false', 'in_app_browser = false', 'hooks = false', 'multi_agent = true',
             '[agents]', 'max_threads = 4', 'max_depth = 1',
             '[permissions.clean-trial.filesystem]']
    lines.extend(f"{json.dumps(k)} = {json.dumps(v)}" for k, v in fs.items())
    lines.extend(['[permissions.clean-trial.network]', 'enabled = false',
                  '[shell_environment_policy]', 'inherit = "none"', '[shell_environment_policy.set]'])
    lines.extend(f"{k} = {json.dumps(v)}" for k, v in env.items())
    lines.extend([f"[projects.{json.dumps(str(work))}]", 'trust_level = "trusted"'])
    (home / "config.toml").write_text("\n".join(lines) + "\n")
    dump(home / "trial-policy.json", {"claude_consultation": "disabled",
                                     "model": "gpt-6.1-sol", "effort": "high"})
    dump(base / "launch.json", {"case": args.case, "workspace": str(work),
                               "codex_home": str(home), "env": env, "codex": str(codex)})


def prepare_deepseek(args, base, work):
    node, harness, credential = args.node, args.harness, args.upstream_credentials
    if node.parent.name != "bin" or node.name != "node":
        raise ValueError("Use a dedicated Node installation with a bin/node executable.")
    if not credential.is_file() or credential.stat().st_mode & (stat.S_IRWXG | stat.S_IRWXO):
        raise ValueError("Upstream credential store must be a private file (chmod 600).")
    modules = harness / "node_modules/@deepseek-ai"
    if json.loads((modules / "dsh/package.json").read_text())["version"] != "0.2.1-rc.5":
        raise ValueError("Install the pinned DeepSeek harness first.")
    case = args.case
    template = ROOT / "reproduction/deepseek" / case
    private = base.parents[1] / ".tools" / f"deepseek-{case}-clean"
    profile = private / "home/profiles/web"
    profile.mkdir(parents=True)
    for name in ("agents", "cache", "tmp"):
        (private / "home" / name).mkdir()
    (private / "home/.credentials.yaml").write_text(
        "version: 1\nrefs:\n  OPENROUTER_API_KEY: " + secrets.token_hex(32) + "\n")
    (profile / "cordis.yml").write_text("[]\n")
    (base / "logs").mkdir()
    replacements = {
        f"{ORIGINAL}/output/deepseek-{case}-clean-api": str(base),
        f"{ORIGINAL}/.tools/deepseek-{case}-clean/home": str(private / "home"),
        f"{ORIGINAL}/.tools/deepseek-harness": str(harness),
        f"{ORIGINAL}/.tools/elan": str(args.elan),
        OLD_NODE: str(node.parent.parent),
        "'.tools/deepseek-harness/node_modules/@deepseek-ai'": json.dumps(str(modules)),
        "'.tools/deepseek-harness/node_modules/@deepseek-ai/dsh-credentials-local/lib/index.js'":
            json.dumps(str(modules / "dsh-credentials-local/lib/index.js")),
        "'.tools/deepseek-appetizer/home/.credentials.yaml'": json.dumps(str(credential)),
        'USER="gspyrou" LOGNAME="gspyrou"': f'USER="{args.user}" LOGNAME="{args.user}"',
        ORIGINAL: str(base.parents[1]),
        '(literal "/Users/gspyrou/Documents/ChatGPT") (literal "/Users/gspyrou/Documents") (literal "/Users/gspyrou")':
            ' '.join(f'(literal {json.dumps(str(p))})' for p in base.parents[1].parents if p != Path("/")),
    }
    for path in [*template.glob("*.mjs"), *template.glob("*.sh"), template / "isolation.sb",
                 *(template / "profile").iterdir(), *(template / "tools").iterdir()]:
        if path.name.startswith("monitor-") or path.name.endswith(".test.mjs"):
            continue
        if path.parent.name == "profile":
            target = profile / path.name
        elif path.parent.name == "tools":
            target = work / "tools" / path.name
        else:
            target = base / path.name
        body = path.read_text()
        pattern = "|".join(re.escape(key) for key in sorted(replacements, key=len, reverse=True))
        body = re.sub(pattern, lambda m: replacements[m[0]], body)
        if path.suffix == ".mjs":
            # Node path.join does not discard the prefix for an absolute path.
            body = re.sub(r'join\(project,\s*("(/[^"\n]+)")\)', r'\1', body)
        if path.name == "isolation.sb":
            if case == "appetizer":
                body += '\n' + ' '.join(f'(allow file-read* (literal {json.dumps(str(p))}))'
                                         for p in private.parents if p != Path("/")) + '\n'
            for path_to_deny in (ROOT, credential):
                rule = "literal" if path_to_deny.is_file() else "subpath"
                body += f'\n(deny file-read* ({rule} {json.dumps(str(path_to_deny))}))\n'
        target.write_text(body)
        if path.suffix == ".sh":
            target.chmod(0o700)
    probe = '''const fs = require("node:fs");
for (const [path, mode] of JSON.parse(process.argv[1])) {
  try { fs.closeSync(fs.openSync(path, mode)); }
  catch (e) { if (["EPERM", "EACCES"].includes(e.code)) continue; throw e; }
  throw new Error("Sandbox allowed forbidden open: " + path);
}
console.log("PASS: release and upstream key denied, source frozen");'''
    checks = [(str(ROOT / "results/deepseek/appetizer/HDP.lean"), "r"),
              (str(credential), "r"), (str(work / "AGENTS.md"), "r+")]
    run(base / "isolated-command.sh", node, "-e", probe, json.dumps(checks))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("model", choices=("codex", "deepseek"))
    parser.add_argument("case", choices=("appetizer", "chapter01"))
    parser.add_argument("pdf", type=Path)
    parser.add_argument("scratch", type=Path, help="Private operator directory outside this checkout")
    parser.add_argument("--stage-only", action="store_true", help="Copy only clean inputs. Skip platform setup.")
    parser.add_argument("--elan", type=Path)
    parser.add_argument("--tool-bin", type=Path, default=Path("/opt/homebrew/bin"))
    for opt in ("workflow", "auth", "codex", "models-cache", "node", "harness", "upstream-credentials"):
        parser.add_argument(f"--{opt}", type=Path)
    args = parser.parse_args()
    for k, v in vars(args).items():
        if isinstance(v, Path):
            setattr(args, k, v.expanduser().resolve())
    args.user = Path.home().name
    if args.scratch.is_relative_to(ROOT) or ROOT.is_relative_to(args.scratch):
        parser.error("Use a separate scratch directory outside the release.")
    if not args.stage_only:
        if sys.platform != "darwin" or not args.scratch.is_relative_to("/Users"):
            parser.error("The original launchers require macOS and scratch under /Users.")
        required = (("elan", "workflow", "auth", "codex") if args.model == "codex"
                    else ("elan", "node", "harness", "upstream_credentials"))
        for field in required:
            if not getattr(args, field):
                parser.error(f"--{field.replace('_', '-')} is required.")
        if any(c in str(p) for p in vars(args).values() if isinstance(p, Path) for c in '"\\\n$\x60'):
            parser.error("Runtime paths must avoid shell/profile metacharacters.")
        if args.model == "deepseek" and (
                not args.upstream_credentials.is_relative_to("/Users")
                or args.upstream_credentials.is_relative_to(args.scratch)):
            parser.error("Use an upstream credential file under /Users outside the run directory.")
    os.umask(0o077)
    base = args.scratch / "output" / f"{args.model}-{args.case}-clean-api"
    base.mkdir(parents=True, exist_ok=False)
    work = base / "workspace"
    spec = seed(args.model, args.case, args.pdf, work)
    if not args.stage_only:
        cache(work, args.elan)
        if args.model == "codex":
            prepare_codex(args, base, work, spec)
        else:
            prepare_deepseek(args, base, work)
            run(base / "isolated-command.sh", work / "tools/lake.sh", "build", "HDP")
    print(base)


if __name__ == "__main__":
    main()
