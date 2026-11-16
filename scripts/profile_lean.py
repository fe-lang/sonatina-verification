#!/usr/bin/env python3
"""Profile fresh Lean source checks with a deadline and machine-readable measurements."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import resource
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
WORKER = "PROFILE_LEAN_WORKER"


def lean_environment():
    """The environment that Lake gives to `lean` for this workspace."""
    printed = subprocess.run(
        ["lake", "env", sys.executable, "-c",
         "import json, os; print(json.dumps(dict(os.environ)))"],
        cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True).stdout
    return json.loads(printed)


def seconds(text):
    match = re.fullmatch(r"([\d.]+)(ms|s)", text)
    return float(match.group(1)) / (1000 if match.group(2) == "ms" else 1)


def phases(log):
    """Cumulative phase times of `lean --profile`, and the longest reported phase of one
    declaration, in seconds."""
    cumulative, slowest, summary = {}, 0.0, False
    for line in log.splitlines():
        if line.startswith("cumulative profiling times"):
            summary = True
        elif summary and line.startswith("\t"):
            name, value = line.strip().rsplit(" ", 1)
            cumulative[name] = seconds(value)
        elif not summary:
            match = re.fullmatch(r"(.+) took ([\d.]+m?s)", line)
            if match and match.group(1) != "import":
                slowest = max(slowest, seconds(match.group(2)))
    return cumulative, slowest


def profile(source, timeout):
    source = source.resolve()
    relative = source.relative_to(ROOT)
    if source.suffix != ".lean" or not source.is_file():
        raise ValueError(f"Not a Lean source: {relative}")
    if (relative.parts[0] == "Draft" or relative == Path("Draft.lean")) and timeout > 60:
        raise ValueError("Draft profiles cannot exceed the 60-second acceptance deadline.")
    output = ROOT / ".lake" / "profiles" / relative.with_suffix("")
    output.parent.mkdir(parents=True, exist_ok=True)
    trace = Path(str(output) + ".trace.json")
    log = Path(str(output) + ".log")
    summary = Path(str(output) + ".json")
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    if trace.exists():
        trace.unlink()
    command = ["lean", "--profile", "-Dprofiler.threshold=10",
               "-Dtrace.profiler=true", "-Dtrace.profiler.threshold=10",
               "-Dtrace.profiler.output.pp=false", f"-Dtrace.profiler.output={trace}",
               str(relative)]
    started = time.monotonic()
    timed_out = False
    with log.open("w") as stream:
        process = subprocess.Popen(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                                   stdin=subprocess.DEVNULL, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
            code = 124
    wall = time.monotonic() - started
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    changed = hashlib.sha256(source.read_bytes()).hexdigest() != source_hash
    if changed:
        code = 1
    cumulative, slowest = phases(log.read_text())
    record = {"source": str(relative), "sha256": source_hash,
              "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
              "host": platform.platform(), "command": command,
              "status": "source-changed" if changed else ("timeout" if timed_out else ("pass" if code == 0 else "fail")),
              "exit_code": code, "timeout_seconds": timeout,
              "wall_seconds": wall,
              "import_seconds": cumulative.get("import", 0.0),
              "elaboration_seconds": cumulative.get("elaboration", 0.0),
              "kernel_seconds": cumulative.get("type checking", 0.0),
              "compilation_seconds": sum(value for name, value in cumulative.items()
                                         if name.startswith("compilation")),
              "slowest_phase_seconds": slowest,
              "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
              "peak_rss_bytes": usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
              "log": str(log.relative_to(ROOT)), "trace": str(trace.relative_to(ROOT))}
    summary.write_text(json.dumps(record, indent=2) + "\n")
    print(f"{relative}: {record['status']}, {wall:.2f}s wall, "
          f"{record['elaboration_seconds'] * 1000:.1f}ms elaboration, "
          f"{record['kernel_seconds'] * 1000:.1f}ms kernel; {summary.relative_to(ROOT)}")
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, nargs="?")
    parser.add_argument("--all-draft", action="store_true")
    parser.add_argument("--timeout", type=float, default=60,
                        help="Wall-clock deadline of the Lean process for one module; "
                             "the Draft acceptance limit is 60 seconds.")
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0 or bool(args.source) == args.all_draft:
        parser.error("Choose a source or --all-draft, with a positive deadline.")
    if args.all_draft and args.timeout > 60:
        parser.error("Draft profiles cannot exceed the 60-second acceptance deadline.")
    if os.environ.get(WORKER):
        return profile(args.source, args.timeout)
    if args.source:
        sources = [args.source.resolve()]
    else:
        sources = sorted((ROOT / "Draft").rglob("*.lean"))
        if (ROOT / "Draft.lean").is_file():
            sources.append(ROOT / "Draft.lean")
        if not sources:
            parser.error("Draft has no Lean sources; an empty profile suite cannot pass.")
    # Lake resolves the environment one time. The measured process is `lean` alone.
    environment = lean_environment()
    environment[WORKER] = "1"
    for source in sources:
        # Separate workers keep child CPU and peak-memory measurements specific to one module.
        result = subprocess.run([sys.executable, str(Path(__file__).resolve()), str(source),
                                 "--timeout", str(args.timeout)], cwd=ROOT, env=environment)
        if result.returncode:
            return result.returncode
    return 0


if __name__ == "__main__":
    sys.exit(main())
