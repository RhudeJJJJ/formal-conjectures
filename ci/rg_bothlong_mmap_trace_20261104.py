"""Fixed, owned-child mmap tracing for the existing BothLong diagnostic.

No attach, detach mode, new session/group, syscall injection or proofstore write.
The fixture only creates its own small files and Python process before restore.
Raw strace timestamps are Unix wall clock; Lean phase markers are monotonic.
Neither trace parsing nor a successful fixture constitutes a Lean proof.
"""
import argparse
import collections
import hashlib
import json
import os
import pathlib
import re
import signal
import stat
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
BUILD_RELATIVE = pathlib.Path("Proofs/RG_Lean_20261019/build/bothlong_phase_probe")
STRACE = pathlib.Path("/usr/bin/strace")
REPORT_NAME = "mmap_trace_control.json"
FIXTURE_DIRECTORY = "mmap_trace_fixture"
FLAGS = ["--kill-on-exit", "-f", "-I", "1", "-yy", "-ttt", "-T",
         "-e", "trace=mmap,munmap,mremap"]
LEAN_FLAGS = ["-j1", "-DElab.async=false", "-DwarningAsError=true",
              "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
              "-Dprofiler=true", "-Dprofiler.threshold=100"]
MODULES = {
    "RGDiagnostic.PhaseMarker",
    "Proofs.RGDiagnosticImportFixture",
    "Proofs.RGDiagnosticMarkerControl",
    "Proofs.RadenkovicGutmanD1OriginalSharedBothLongPhaseProbe",
}
FIXTURE_BYTES = 4096
READY_TIMEOUT_SECONDS = 5.0
KILL_AT_SECONDS = 2.0
TRACER_WAIT_SECONDS = 3.0
TRACEE_END_TIMEOUT_SECONDS = 3.0
FIXTURE_SELF_EXIT_SECONDS = 15.0
SELF_EXIT_MARGIN_SECONDS = 1.0
TAIL_LIMIT = 32
FIXTURE_PROGRAM = r"""
import json, mmap, os, pathlib, time
obj, ready = map(pathlib.Path, __import__('sys').argv[1:3])
with obj.open('rb') as stream:
    mapping = mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ)
    assert mapping[0] == 82
    text = pathlib.Path('/proc/self/stat').read_text()
    fields = text[text.rfind(')') + 2:].split()
    value = dict(pid=os.getpid(), start_time_ticks=int(fields[19]),
                 parent_pid=int(fields[1]), process_group=int(fields[2]),
                 fixture_path=str(obj), fixture_bytes=obj.stat().st_size)
    pending_ready = ready.with_suffix('.pending')
    with pending_ready.open('x') as out:
        json.dump(value, out, sort_keys=True)
        out.flush()
        os.fsync(out.fileno())
    pending_ready.replace(ready)
    time.sleep(15.0)
    mapping.close()
"""


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def file_sha(path):
    with pathlib.Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Repeated JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(pathlib.Path(path).read_bytes(), object_pairs_hook=unique)


def write_new_json(path, value):
    raw = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, "wb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def native_context(build):
    build = pathlib.Path(build)
    require(os.environ.get("GITHUB_ACTIONS") == "true", "Not a native Actions context")
    require(os.environ.get("RUNNER_ENVIRONMENT") == "github-hosted" and
            os.environ.get("RUNNER_OS") == "Linux", "Not a fresh hosted Linux runner")
    workspace = pathlib.Path(os.environ["GITHUB_WORKSPACE"]).resolve(strict=True)
    require(workspace == ROOT and workspace.is_relative_to("/home/runner/work"),
            "Helper is outside the fixed hosted checkout")
    require(build == workspace / BUILD_RELATIVE and build.resolve() == build,
            "Not the fixed direct diagnostic build directory")
    expected_ref = "refs/heads/rg-d1-bothlong-phase-probe-20261104"
    repository = "RhudeJJJJ/formal-conjectures"
    require(os.environ.get("GITHUB_REPOSITORY") == repository and
            os.environ.get("GITHUB_REF") == expected_ref, "Not the fixed personal diagnostic branch")
    values = {k: os.environ.get(k) for k in
              ("GITHUB_REPOSITORY", "GITHUB_REF", "GITHUB_SHA", "GITHUB_RUN_ID",
               "GITHUB_RUN_ATTEMPT", "GITHUB_JOB", "GITHUB_WORKFLOW_REF")}
    require(re.fullmatch(r"[0-9a-f]{40}", values["GITHUB_SHA"] or "") is not None,
            "Missing native source commit")
    require(all(re.fullmatch(r"[1-9][0-9]*", values[k] or "") for k in
                ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT")), "Missing native run/attempt")
    require(values["GITHUB_JOB"] == "diagnose", "Not the fixed diagnostic job")
    require(values["GITHUB_WORKFLOW_REF"] ==
            repository + "/.github/workflows/rg-d1-bothlong-phase-probe-20261104.yml@" + expected_ref,
            "Wrong native workflow ref")
    return values


def strace_identity():
    require(proc_namespace_observation()["same_pid_namespace"],
            "Python process IDs and visible /proc use different namespaces; cannot bind owned processes")
    require(STRACE.resolve(strict=True) == STRACE and STRACE.is_file() and
            not STRACE.is_symlink(), "The fixed strace executable is unavailable")
    result = subprocess.run([str(STRACE), "--version"], capture_output=True,
                            text=True, timeout=5, check=False)
    require(result.returncode == 0, "strace --version failed: " + result.stderr)
    match = re.search(r"\bversion\s+([0-9]+)\.([0-9]+)(?:\.([0-9]+))?", result.stdout)
    require(match is not None, "Unrecognized strace version")
    version = [int(match[1]), int(match[2]), int(match[3] or 0)]
    require(tuple(version[:2]) >= (6, 6), "strace >= 6.6 is required for --kill-on-exit")
    return dict(path=str(STRACE), bytes=STRACE.stat().st_size, sha256=file_sha(STRACE),
                version=version, version_stdout=result.stdout, version_stderr=result.stderr,
                version_returncode=result.returncode)


def proc_identity(pid):
    try:
        raw = pathlib.Path(f"/proc/{pid}/stat").read_text()
    except FileNotFoundError:
        return dict(pid=pid, status="GONE")
    end = raw.rfind(")")
    require(end >= 0 and int(raw[:raw.find(" ")]) == pid, "Malformed process stat")
    values = raw[end + 2:].split()
    return dict(pid=pid, status="READ", state=values[0], parent_pid=int(values[1]),
                process_group=int(values[2]), start_time_ticks=int(values[19]))


def proc_namespace_observation():
    raw = pathlib.Path("/proc/self/stat").read_text()
    fields = raw[raw.rfind(")") + 2:].split()
    value = dict(python_pid=os.getpid(), python_parent_pid=os.getppid(),
                 python_process_group=os.getpgrp(),
                 proc_self_pid=int(raw[:raw.find(" ")]),
                 proc_self_parent_pid=int(fields[1]), proc_self_process_group=int(fields[2]))
    value["same_pid_namespace"] = (
        value["python_pid"] == value["proc_self_pid"] and
        value["python_parent_pid"] == value["proc_self_parent_pid"] and
        value["python_process_group"] == value["proc_self_process_group"])
    return value


def original_process_ended(identity, current):
    return (current["status"] == "GONE" or
            current.get("start_time_ticks") != identity["start_time_ticks"] or
            current.get("state") == "Z")


def split_arguments(text):
    result, start, nesting, quoted, escaped = [], 0, [], False, False
    for index, char in enumerate(text):
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == '"':
            quoted = not quoted
            continue
        if quoted:
            continue
        if char in "(<[{":
            nesting.append(char)
        elif char in ")>]}":
            require(bool(nesting), "Unbalanced syscall argument")
            nesting.pop()
        elif char == "," and not nesting:
            result.append(text[start:index].strip())
            start = index + 1
    require(not quoted and not nesting, "Unfinished syscall arguments")
    result.append(text[start:].strip())
    return result


def integer_argument(value):
    return int(value, 16 if value.startswith("0x") else 10) if re.fullmatch(
        r"(?:0x[0-9a-fA-F]+|[0-9]+)", value) else None


def parsed_call(body, pid, stamp, first_line, last_line, resumed=False, end_stamp=None):
    match = re.fullmatch(r"(mmap|munmap|mremap)\((.*)\)\s+=\s+(.+)", body)
    if match is None:
        return None
    syscall, args_raw, returned = match.groups()
    args = split_arguments(args_raw)
    duration = re.search(r"\s+<([0-9]+\.[0-9]+)>$", returned)
    seconds = duration[1] if duration else None
    if duration:
        returned = returned[:duration.start()].rstrip()
    error = re.match(r"-1\s+([A-Z][A-Z0-9_]+)\b", returned)
    if error:
        outcome, errno = "ERROR", error[1]
    elif re.fullmatch(r"(?:0x[0-9a-fA-F]+|0|NULL)", returned):
        outcome, errno = "SUCCESS", None
    else:
        outcome, errno = "UNKNOWN_RETURN", None
    row = dict(pid=pid, syscall=syscall, first_trace_line_wallclock_unix_seconds=stamp,
               last_trace_line_wallclock_unix_seconds=end_stamp or stamp, first_line=first_line,
               last_line=last_line, resumed=resumed, duration_seconds=seconds,
               arguments=args, result_text=returned, outcome=outcome, errno=errno,
               requested_address=args[0] if args else None,
               length_bytes=None, file_descriptor=None, file_path=None, offset_bytes=None)
    if syscall == "mmap":
        require(len(args) == 6, "Unrecognized mmap argument count")
        row["length_bytes"] = integer_argument(args[1])
        row["protection"], row["mapping_flags"] = args[2], args[3]
        fd = re.fullmatch(r"(-?[0-9]+)(?:<(.*)>)?", args[4])
        if fd:
            row["file_descriptor"] = int(fd[1])
            row["file_path"] = fd[2]
        row["offset_bytes"] = integer_argument(args[5])
    elif syscall == "munmap":
        require(len(args) == 2, "Unrecognized munmap argument count")
        row["length_bytes"] = integer_argument(args[1])
    else:
        require(len(args) in (4, 5), "Unrecognized mremap argument count")
        row["old_length_bytes"] = integer_argument(args[1])
        row["length_bytes"] = integer_argument(args[2])
        row["mapping_flags"] = args[3]
    return row


def _read_trace(path, on_call=None):
    """Stream all raw bytes; unresolved syntax remains explicit diagnostic data."""
    path = pathlib.Path(path)
    require(path.is_file() and not path.is_symlink(), "Raw trace is unavailable")
    digest, byte_count = hashlib.sha256(), 0
    count = collections.Counter({k: 0 for k in (
        "raw_lines", "complete_calls", "mmap_total", "mmap_file", "mmap_errors",
        "munmap_total", "munmap_errors", "mremap_total", "mremap_errors",
        "unknown_outcomes", "unfinished_lines", "resumed_lines", "matched_resumptions",
        "unresolved_unfinished", "unmatched_resumed", "unparsed_lines", "signal_lines")})
    pending, pids, terminal = {}, set(), {}
    first_pid = None
    last_mappings = collections.deque(maxlen=TAIL_LIMIT)
    unparsed, abandoned, unmatched = (collections.deque(maxlen=TAIL_LIMIT) for _ in range(3))
    prefix = re.compile(r"^\s*(?:\[pid\s+([0-9]+)\]|([0-9]+))\s+([0-9]+\.[0-9]+)\s+(.*)$")
    with path.open("rb") as stream:
        for number, raw in enumerate(stream, 1):
            digest.update(raw)
            byte_count += len(raw)
            count["raw_lines"] += 1
            try:
                line = raw.decode().rstrip("\r\n")
            except UnicodeDecodeError:
                count["unparsed_lines"] += 1
                unparsed.append(dict(line=number, reason="NON_UTF8", raw_prefix_hex=raw[:128].hex()))
                continue
            matched = prefix.fullmatch(line)
            if matched is None:
                count["unparsed_lines"] += 1
                unparsed.append(dict(line=number, reason="UNRECOGNIZED_PID_TIMESTAMP", text=line[:1200]))
                continue
            pid, stamp, body = int(matched[1] or matched[2]), matched[3], matched[4]
            if first_pid is None:
                first_pid = pid
            pids.add(pid)
            exited = re.fullmatch(r"\+\+\+ exited with ([0-9]+) \+\+\+", body)
            killed = re.fullmatch(r"\+\+\+ killed by ([A-Z][A-Z0-9_]+)(?: \(core dumped\))? \+\+\+", body)
            if exited or killed:
                terminal[str(pid)] = dict(exit_code=int(exited[1]) if exited else None,
                    signal=killed[1] if killed else None, wallclock_unix_seconds=stamp, line=number)
                continue
            if body.startswith("--- ") and body.endswith(" ---"):
                count["signal_lines"] += 1
                continue
            if body.endswith("<unfinished ...>"):
                count["unfinished_lines"] += 1
                if pid in pending:
                    count["unresolved_unfinished"] += 1
                    abandoned.append(pending[pid])
                pending[pid] = dict(pid=pid, line=number, timestamp=stamp,
                                    body=body.removesuffix("<unfinished ...>").rstrip())
                continue
            start, start_stamp, was_resumed = number, stamp, False
            resumed = re.match(r"^<\.\.\. (mmap|munmap|mremap) resumed>(.*)$", body)
            if resumed:
                count["resumed_lines"] += 1
                previous = pending.pop(pid, None)
                if previous is None or not previous["body"].startswith(resumed[1] + "("):
                    count["unmatched_resumed"] += 1
                    unmatched.append(dict(line=number, pid=pid, text=body[:1200]))
                    if previous is not None:
                        count["unresolved_unfinished"] += 1
                        abandoned.append(previous)
                    continue
                body = previous["body"] + resumed[2]
                start, start_stamp, was_resumed = previous["line"], previous["timestamp"], True
                count["matched_resumptions"] += 1
            try:
                call = parsed_call(body, pid, start_stamp, start, number, was_resumed, stamp)
            except (RuntimeError, ValueError) as error:
                call = None
                reason = str(error)
            else:
                reason = "UNRECOGNIZED_COMPLETE_SYSCALL"
            if call is None:
                count["unparsed_lines"] += 1
                unparsed.append(dict(line=number, pid=pid, reason=reason, text=body[:1200]))
                continue
            count["complete_calls"] += 1
            count[call["syscall"] + "_total"] += 1
            if call["outcome"] == "ERROR":
                count[call["syscall"] + "_errors"] += 1
            elif call["outcome"] == "UNKNOWN_RETURN":
                count["unknown_outcomes"] += 1
            if call["syscall"] == "mmap" and call["file_descriptor"] is not None and \
                    call["file_descriptor"] >= 0 and "MAP_ANONYMOUS" not in call["mapping_flags"]:
                count["mmap_file"] += 1
            if call["syscall"] in ("mmap", "mremap"):
                last_mappings.append(call)
            if on_call is not None:
                on_call(call)
    count["unresolved_unfinished"] += len(pending)
    unresolved = list(abandoned) + list(pending.values())
    return dict(schema="RG_MMAP_SYSCALL_OBSERVATION_V1", trace_path=str(path),
        trace_bytes=byte_count, trace_sha256=digest.hexdigest(),
        timestamp_kind="UNIX_WALL_CLOCK_SECONDS",
        duration_kind="STRACE_RECORDED_SYSCALL_SECONDS",
        lean_marker_timestamps_are_separate_monotonic_clock=True,
        first_observed_pid=first_pid, observed_pids=sorted(pids),
        main_pid=None, main_exit_code=None, main_signal=None,
        main_identity_basis="NOT_PROVEN_BY_MMAP_ONLY_FILTER; correlate with independent PID/start_ticks",
        per_pid_terminal=terminal, counts=dict(count), last_mappings=list(last_mappings),
        unresolved_unfinished=unresolved[-TAIL_LIMIT:],
        unmatched_resumed=list(unmatched), unparsed_examples=list(unparsed),
        detail_lists_are_bounded_but_counters_and_raw_trace_are_complete=True,
        raw_trace_retained=True, trace_success_claim=False,
        original_kernel_export_claim=False, family_closure_claim=False)


def summarize_trace(path):
    return _read_trace(path)


def require_fixture_mapping(trace_path, fixture_object):
    """Require a complete exact-file mmap attempt, including a recorded failure."""
    fixture = pathlib.Path(fixture_object)
    require(fixture.is_absolute() and fixture.resolve(strict=True) == fixture and
            fixture.is_file() and not fixture.is_symlink(), "Fixture object is not exact and regular")
    size = fixture.stat().st_size
    require(size > 0, "Fixture object is empty")
    matches = collections.deque(maxlen=TAIL_LIMIT)
    counts = collections.Counter({"complete_exact_file_attempts": 0, "successful_mmaps": 0,
                                  "failed_mmaps": 0})

    def observe(call):
        if call["syscall"] == "mmap" and call["file_path"] == str(fixture) and \
                call["length_bytes"] == size and call["offset_bytes"] == 0 and \
                call["outcome"] in ("SUCCESS", "ERROR"):
            counts["complete_exact_file_attempts"] += 1
            counts["successful_mmaps" if call["outcome"] == "SUCCESS" else "failed_mmaps"] += 1
            matches.append(call)

    summary = _read_trace(trace_path, observe)
    require(counts["complete_exact_file_attempts"] > 0,
            "No complete exact-path, exact-size fixture mmap attempt in actual trace")
    return dict(fixture_path=str(fixture), fixture_bytes=size, fixture_sha256=file_sha(fixture),
                trace_bytes=summary["trace_bytes"], trace_sha256=summary["trace_sha256"],
                **dict(counts), last_matching_attempts=list(matches),
                mapping_failure_is_observation_not_lean_failure=True,
                actual_lean_control_success_must_be_checked_separately=True)


def _wrapper(command, trace_path):
    return [str(STRACE), *FLAGS, "-o", str(trace_path), "--", *command]


def _fixture(directory):
    """One real fixture; signal only our Popen tracer, never a parsed trace PID."""
    directory = pathlib.Path(directory)
    require(directory.is_absolute() and directory.resolve(strict=True) == directory and
            directory.is_dir() and not any(directory.iterdir()), "Fixture directory must be new and empty")
    fixture = directory / "fixture.bin"
    ready = directory / "tracee_ready.json"
    trace = directory / "fixture.mmap.log"
    stdout, stderr = directory / "tracer.stdout.log", directory / "tracer.stderr.log"
    report = dict(success=False, directory=str(directory), process_group_changed=False,
                  tracee_signals_sent=[], fixture_program_sha256=hashlib.sha256(
                      FIXTURE_PROGRAM.encode()).hexdigest(), fixture_self_exit_seconds=FIXTURE_SELF_EXIT_SECONDS,
                  kill_at_seconds=KILL_AT_SECONDS, tracee_end_timeout_seconds=TRACEE_END_TIMEOUT_SECONDS)
    proc, tracer_identity, tracee_identity = None, None, None
    spawn_time = None
    began = time.monotonic()

    def kill_owned_tracer():
        current = proc_identity(proc.pid)
        require(current.get("start_time_ticks") == tracer_identity["start_time_ticks"],
                "Owned tracer identity changed before kill")
        proc.kill()
        report["tracer_signal_sent"] = "SIGKILL"
        report["tracer_kill_at_elapsed_seconds"] = round(time.monotonic() - began, 6)
        report["tracer_kill_at_spawn_elapsed_seconds"] = round(time.monotonic() - spawn_time, 6)

    try:
        report["proc_namespace_before_spawn"] = proc_namespace_observation()
        require(report["proc_namespace_before_spawn"]["same_pid_namespace"],
                "Python process IDs and visible /proc use different namespaces; cannot bind owned processes")
        with fixture.open("xb") as stream:
            stream.write(b"R" * FIXTURE_BYTES)
        command = [sys.executable, "-I", "-c", FIXTURE_PROGRAM, str(fixture), str(ready)]
        report["fixture_object"] = dict(path=str(fixture), bytes=FIXTURE_BYTES, sha256=file_sha(fixture))
        report["command"] = _wrapper(command, trace)
        with stdout.open("xb") as out, stderr.open("xb") as err:
            spawn_time = time.monotonic()
            report["earliest_natural_self_exit_spawn_elapsed_seconds"] = FIXTURE_SELF_EXIT_SECONDS
            report["self_exit_separation_margin_seconds"] = SELF_EXIT_MARGIN_SECONDS
            proc = subprocess.Popen(report["command"], stdout=out, stderr=err, cwd=directory)
            tracer_identity = proc_identity(proc.pid)
            report["tracer_identity_before"] = tracer_identity
            require(tracer_identity["status"] == "READ" and
                    tracer_identity["parent_pid"] == os.getpid() and
                    tracer_identity["process_group"] == os.getpgrp(), "Tracer is not our same-group child")
            while not ready.exists() and proc.poll() is None and \
                    time.monotonic() - spawn_time < READY_TIMEOUT_SECONDS:
                time.sleep(0.025)
            require(ready.is_file(), "The actual traced fixture did not become ready")
            report["ready_at_spawn_elapsed_seconds"] = round(time.monotonic() - spawn_time, 6)
            require(report["ready_at_spawn_elapsed_seconds"] <= READY_TIMEOUT_SECONDS,
                    "Fixture readiness exceeded its fixed deadline")
            fixture_ready = read_json(ready)
            tracee_identity = proc_identity(fixture_ready["pid"])
            report["fixture_ready"] = fixture_ready
            report["tracee_identity_before"] = tracee_identity
            require(tracee_identity["status"] == "READ" and
                    tracee_identity["start_time_ticks"] == fixture_ready["start_time_ticks"] and
                    tracee_identity["parent_pid"] == proc.pid and
                    tracee_identity["process_group"] == os.getpgrp(), "Tracee PID/start/group is not bound")
            require(fixture_ready["fixture_path"] == str(fixture) and
                    fixture_ready["fixture_bytes"] == FIXTURE_BYTES, "Wrong actual fixture mapping")
            status = pathlib.Path(f"/proc/{tracee_identity['pid']}/status").read_text()
            tracer_pid = int(re.search(r"^TracerPid:\s+([0-9]+)$", status, re.M)[1])
            report["observed_tracee_tracer_pid"] = tracer_pid
            require(tracer_pid == proc.pid, "Fixture is not actually traced by our tracer")
            while time.monotonic() - spawn_time < KILL_AT_SECONDS:
                time.sleep(max(0.0, min(0.025, KILL_AT_SECONDS - (time.monotonic() - spawn_time))))
            require(proc.poll() is None, "Tracer exited before the owned kill")
            prekill = proc_identity(tracee_identity["pid"])
            report["tracee_identity_immediately_before_kill"] = prekill
            require(prekill["status"] == "READ" and
                    prekill["start_time_ticks"] == tracee_identity["start_time_ticks"] and
                    prekill["state"] not in ("Z", "X", "x") and
                    prekill["parent_pid"] == proc.pid and
                    prekill["process_group"] == tracer_identity["process_group"],
                    "Tracee was not still the same live child immediately before the kill")
            status = pathlib.Path(f"/proc/{tracee_identity['pid']}/status").read_text()
            report["tracee_tracer_pid_immediately_before_kill"] = int(
                re.search(r"^TracerPid:\s+([0-9]+)$", status, re.M)[1])
            require(report["tracee_tracer_pid_immediately_before_kill"] == proc.pid,
                    "Tracee was not still attached to our owned tracer immediately before kill")
            report["prekill_at_spawn_elapsed_seconds"] = round(time.monotonic() - spawn_time, 6)
            report["latest_planned_end_observation_spawn_elapsed_seconds"] = (
                report["prekill_at_spawn_elapsed_seconds"] + TRACER_WAIT_SECONDS +
                TRACEE_END_TIMEOUT_SECONDS)
            require(report["latest_planned_end_observation_spawn_elapsed_seconds"] <
                    FIXTURE_SELF_EXIT_SECONDS - SELF_EXIT_MARGIN_SECONDS,
                    "Lifecycle observation would overlap the fixture's possible natural exit")
            kill_owned_tracer()
            report["tracer_returncode"] = proc.wait(timeout=TRACER_WAIT_SECONDS)
            deadline = time.monotonic() + TRACEE_END_TIMEOUT_SECONDS
            while True:
                current = proc_identity(tracee_identity["pid"])
                if original_process_ended(tracee_identity, current) or time.monotonic() >= deadline:
                    break
                time.sleep(0.025)
            report["tracee_identity_after"] = current
            report["tracee_end_observed_spawn_elapsed_seconds"] = round(time.monotonic() - spawn_time, 6)
            report["tracee_ended_after_owned_tracer_kill"] = original_process_ended(tracee_identity, current)
            require(report["tracer_returncode"] == -signal.SIGKILL,
                    "Owned tracer was not terminated by the intended SIGKILL")
            require(report["tracee_ended_after_owned_tracer_kill"],
                    "--kill-on-exit did not terminate the identity-bound tracee within the fixed observation")
            require(report["tracee_end_observed_spawn_elapsed_seconds"] <
                    FIXTURE_SELF_EXIT_SECONDS - SELF_EXIT_MARGIN_SECONDS,
                    "Observed tracee end was too late to distinguish natural self-exit")
        report["mapping"] = require_fixture_mapping(trace, fixture)
        require(report["mapping"]["successful_mmaps"] >= 1, "The own fixture had no successful real mmap")
        require(any(m["pid"] == tracee_identity["pid"] and m["outcome"] == "SUCCESS"
                    for m in report["mapping"]["last_matching_attempts"]),
                "Successful fixture mmap was not made by the bound tracee")
        report["success"] = True
    except Exception as error:
        report["error"] = f"{type(error).__name__}: {error}"
    finally:
        if proc is not None and proc.poll() is None:
            try:
                kill_owned_tracer()
                report["tracer_returncode"] = proc.wait(timeout=TRACER_WAIT_SECONDS)
            except Exception as error:
                report["cleanup_error"] = f"{type(error).__name__}: {error}"
                report["success"] = False
        if tracee_identity is not None and not original_process_ended(
                tracee_identity, proc_identity(tracee_identity["pid"])):
            # No direct tracee signal: the small fixture ends itself after15s.
            deadline = began + READY_TIMEOUT_SECONDS + FIXTURE_SELF_EXIT_SECONDS + 1
            while time.monotonic() < deadline:
                current = proc_identity(tracee_identity["pid"])
                if original_process_ended(tracee_identity, current):
                    break
                time.sleep(0.05)
            report["tracee_final_cleanup_observation"] = proc_identity(tracee_identity["pid"])
            report["success"] = False
        report["elapsed_seconds"] = round(time.monotonic() - began, 6)
        report["files"] = {p.name: dict(bytes=p.stat().st_size, sha256=file_sha(p))
                           for p in (fixture, ready, trace, stdout, stderr) if p.is_file()}
        if trace.is_file():
            try:
                report["trace_summary"] = summarize_trace(trace)
            except Exception as error:
                report["trace_parse_error"] = f"{type(error).__name__}: {error}"
                report["success"] = False
    return report


def _base_report(kind):
    return dict(kind=kind, status="MMAP_TRACE_CONTROL_REJECTED",
                helper_sha256=file_sha(pathlib.Path(__file__)), wrapper_flags=FLAGS,
                native_ids=None, original_kernel_export_claim=False, family_closure_claim=False,
                limits_changed=False, proofstore_modified=False, new_process_group_created=False)


def run_local_fixture_control(new_temp_directory):
    """Explicit local fixture entry point. Never supplies or spoofs GH context."""
    directory = pathlib.Path(new_temp_directory).resolve(strict=True)
    report = _base_report("LOCAL_CONTROL_NO_LEAN_PROOF")
    try:
        report["strace"] = strace_identity()
        report["fixture"] = _fixture(directory)
        if report["fixture"]["success"]:
            report["status"] = "LOCAL_CONTROL_NO_LEAN_PROOF_PASSED"
    except Exception as error:
        report["error"] = f"{type(error).__name__}: {error}"
    finally:
        write_new_json(directory / REPORT_NAME, report)
    return report


def require_control(build):
    build = pathlib.Path(build)
    native = native_context(build)
    path = build / REPORT_NAME
    require(path.is_file() and not path.is_symlink(), "Actual lifecycle control report is missing")
    report = read_json(path)
    require(report["kind"] == "FIXED_GITHUB_OWNED_MMAP_LIFECYCLE_CONTROL" and
            report["status"] == "GH_OWNED_MMAP_TRACE_CONTROL_PASSED",
            "A successful actual GH control is required; local reports are not eligible")
    require(report["native_ids"] == native and report["helper_sha256"] ==
            file_sha(pathlib.Path(__file__)), "Control belongs to another native origin/helper")
    require(report["strace"] == strace_identity() and report["wrapper_flags"] == FLAGS,
            "Actual strace executable/version/wrapper changed")
    require(report["production_restore_absent_during_control"] is True and
            not report["original_kernel_export_claim"] and not report["family_closure_claim"],
            "Control scope is not the isolated early fixture")
    fixture = report["fixture"]
    directory = build / FIXTURE_DIRECTORY
    require(fixture["success"] is True and fixture["directory"] == str(directory) and
            fixture["tracer_returncode"] == -signal.SIGKILL and
            fixture["tracer_signal_sent"] == "SIGKILL" and
            fixture["tracee_ended_after_owned_tracer_kill"] is True and
            fixture["tracee_signals_sent"] == [] and fixture["process_group_changed"] is False,
            "Actual owned lifecycle control did not pass")
    process_context = fixture["proc_namespace_before_spawn"]
    require(process_context["same_pid_namespace"] is True and
            process_context["python_pid"] == process_context["proc_self_pid"] and
            process_context["python_parent_pid"] == process_context["proc_self_parent_pid"] and
            process_context["python_process_group"] == process_context["proc_self_process_group"] and
            fixture["tracer_identity_before"]["parent_pid"] == process_context["python_pid"] and
            fixture["tracer_identity_before"]["process_group"] == process_context["python_process_group"],
            "Stored process namespace does not bind the owned tracer")
    before, after = fixture["tracee_identity_before"], fixture["tracee_identity_after"]
    require(original_process_ended(before, after), "Stored tracee end observation is inconsistent")
    prekill = fixture["tracee_identity_immediately_before_kill"]
    require(prekill["status"] == "READ" and prekill["pid"] == before["pid"] and
            prekill["start_time_ticks"] == before["start_time_ticks"] and
            prekill["state"] not in ("Z", "X", "x") and
            prekill["parent_pid"] == fixture["tracer_identity_before"]["pid"] and
            prekill["process_group"] == fixture["tracer_identity_before"]["process_group"] and
            fixture["tracee_tracer_pid_immediately_before_kill"] == fixture["tracer_identity_before"]["pid"],
            "Stored pre-kill tracee was not alive, identical and actually attached")
    require(fixture["fixture_program_sha256"] == hashlib.sha256(FIXTURE_PROGRAM.encode()).hexdigest() and
            fixture["fixture_self_exit_seconds"] == FIXTURE_SELF_EXIT_SECONDS and
            fixture["earliest_natural_self_exit_spawn_elapsed_seconds"] == FIXTURE_SELF_EXIT_SECONDS and
            fixture["self_exit_separation_margin_seconds"] == SELF_EXIT_MARGIN_SECONDS and
            0 <= fixture["ready_at_spawn_elapsed_seconds"] <= READY_TIMEOUT_SECONDS and
            fixture["ready_at_spawn_elapsed_seconds"] <= fixture["prekill_at_spawn_elapsed_seconds"] <=
            fixture["tracer_kill_at_spawn_elapsed_seconds"] <=
            fixture["tracee_end_observed_spawn_elapsed_seconds"] <
            FIXTURE_SELF_EXIT_SECONDS - SELF_EXIT_MARGIN_SECONDS and
            fixture["latest_planned_end_observation_spawn_elapsed_seconds"] ==
            fixture["prekill_at_spawn_elapsed_seconds"] + TRACER_WAIT_SECONDS + TRACEE_END_TIMEOUT_SECONDS and
            fixture["latest_planned_end_observation_spawn_elapsed_seconds"] <
            FIXTURE_SELF_EXIT_SECONDS - SELF_EXIT_MARGIN_SECONDS,
            "Stored lifecycle times do not distinguish EXITKILL from natural self-exit")
    require(fixture["observed_tracee_tracer_pid"] == fixture["tracer_identity_before"]["pid"] and
            before["parent_pid"] == fixture["tracer_identity_before"]["pid"] and
            before["start_time_ticks"] == fixture["fixture_ready"]["start_time_ticks"],
            "Stored actual process identities do not join")
    for name, item in fixture["files"].items():
        candidate = directory / name
        require(pathlib.PurePath(name).name == name and candidate.is_file() and
                not candidate.is_symlink() and candidate.stat().st_size == item["bytes"] and
                file_sha(candidate) == item["sha256"], "Changed lifecycle evidence bytes")
    require(summarize_trace(directory / "fixture.mmap.log") == fixture["trace_summary"],
            "Changed actual lifecycle raw trace")
    require(require_fixture_mapping(directory / "fixture.mmap.log", directory / "fixture.bin") ==
            fixture["mapping"] and fixture["mapping"]["successful_mmaps"] >= 1,
            "Changed actual successful own-fixture mapping")
    return report


def wrap_lean_command(command, trace_path, build):
    build, trace_path = pathlib.Path(build), pathlib.Path(trace_path)
    require_control(build)
    require(isinstance(command, list) and all(isinstance(x, str) and x for x in command),
            "Expected an unchanged direct Lean command list")
    require(pathlib.Path(command[0]).is_absolute() and pathlib.Path(command[0]).name == "lean",
            "Only the direct fixed Lean executable can be traced")
    require(command[1:1 + len(LEAN_FLAGS)] == LEAN_FLAGS, "Strict Lean flags changed")
    require(trace_path.is_absolute() and trace_path.parent == build and
            trace_path.resolve() == trace_path and not trace_path.exists() and
            not trace_path.is_symlink(), "Trace must be a new direct file in the fixed build")
    names = {n + ".mmap.log": n for n in MODULES}
    require(trace_path.name in names, "Trace is not one of the four fixed diagnostic modules")
    name = names[trace_path.name]
    source_root = ROOT / "ci/rg_bothlong_phase_probe_20261104"
    if name == "Proofs.RGDiagnosticImportFixture":
        source_root /= "control_imports"
    expected_source = source_root / (name.replace(".", "/") + ".lean")
    output_root = build / ("helper_objects" if name == "RGDiagnostic.PhaseMarker" else
                           "control_imports" if name == "Proofs.RGDiagnosticImportFixture" else
                           "probe_objects")
    pending = (output_root / (name.replace(".", "/") + ".olean")).with_suffix(".olean.pending")
    require(command == [command[0], *LEAN_FLAGS, "-R", str(source_root),
                        "-o", str(pending), str(expected_source)],
            "Trace command differs from the unchanged exact direct Lean invocation")
    wrapped = _wrapper(command, trace_path)
    require(wrapped[-len(command):] == command, "Lean command tail was altered")
    return wrapped


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--control", action="store_true", required=True)
    parser.parse_args()
    build = ROOT / BUILD_RELATIVE
    require(build.resolve() == build, "Diagnostic build traverses a symlink")
    build.mkdir(parents=True, exist_ok=True)
    report = _base_report("FIXED_GITHUB_OWNED_MMAP_LIFECYCLE_CONTROL")
    try:
        report["native_ids"] = native_context(build)
        require(not (ROOT / "Proofs/RG_Lean_20261019/build/extension").exists(),
                "Lifecycle control must precede all original object restoration")
        report["production_restore_absent_during_control"] = True
        report["strace"] = strace_identity()
        directory = build / FIXTURE_DIRECTORY
        directory.mkdir(exist_ok=False)
        report["fixture"] = _fixture(directory)
        if report["fixture"]["success"]:
            report["status"] = "GH_OWNED_MMAP_TRACE_CONTROL_PASSED"
    except Exception as error:
        report["error"] = f"{type(error).__name__}: {error}"
    finally:
        write_new_json(build / REPORT_NAME, report)
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    return 0 if report["status"] == "GH_OWNED_MMAP_TRACE_CONTROL_PASSED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
