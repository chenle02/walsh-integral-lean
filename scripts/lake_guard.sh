#!/usr/bin/env bash
# Guards for a fresh, unshadowed Lake build (template: Le-AI-Lab templates/lean-package-verify, owner lean-ops).
# Checked against the Lake sources of Lean 4.34.1 and 4.35.0-rc2. Copy into the package's scripts/.
#
# usage:
#   lake_guard.sh shadow LEAN_PATH ROOT_LIB_DIR ROOT...
#       Refuse when a LEAN_PATH entry other than ROOT_LIB_DIR (the root package's .lake/build/lib/lean)
#       holds ROOT/, ROOT.olean or ROOT.ilean for a root library namespace ROOT. Lake puts the root's lib
#       dir LAST on LEAN_PATH (Workspace.leanPath) and Lean takes the FIRST entry that has the module, so
#       such a file in a dependency's .lake shadows the package under `lake env lean` (G14).
#   lake_guard.sh fresh BUILD_LOG ROOT...
#       Refuse when the log of `lake build -v --log-level info --no-ansi` shows a root module that was not
#       built: the job verbs Reused (local artifact cache), Replayed (an earlier build's outputs), Unpacked
#       (an archive) and Fetched (a remote cache), or their -ing forms (Lake/Build/Job/Basic.lean,
#       JobAction.verb). A reused module shows no `sorry` warning (G15). Without -v Lake hides Reused and
#       Replayed jobs (Lake/Build/Run.lean, minAction).
#   lake_guard.sh lean-error LOG PATTERN
#       Succeed when PATTERN (ERE) occurs in a Lean error diagnostic (`FILE:L:C: error: ...` or `error: ...`),
#       never in other output: a declaration named actual_maximum_square in an info line is not a match.
#   lake_guard.sh witness SRC LOG EXIT
#       Refuse a negative-control witness (the positive part of a control, compiled on its own) unless
#       `lake lean SRC` exited 0 with no error, no `declaration uses sorry` warning and no failed Lake job,
#       and SRC (comments stripped) has no `sorry`, `admit` or `axiom`.
#   lake_guard.sh negative-control [--legacy] SRC LOG EXIT [WITNESS_MODULE]
#       Succeed only when the control SRC was rejected for the intended reason: EXIT (of `lake lean SRC`) is 1,
#       LOG has at least one error, EVERY error is `unsolved goals`, and every goal block of every error ends
#       in exactly `⊢ False`. Diagnostics are parsed as blocks (a message runs until the next header
#       `FILE:L:C: error|warning|info[(tag)]:`, Lake's `error|warning|info: FILE:L:C:` replay, or a Lake job
#       line), so warnings and infos are allowed anywhere and never truncate a goal. SRC must not contain
#       `sorry`, `admit` or `axiom`, must `import WITNESS_MODULE`, and must declare nothing but `example`s
#       (positive helpers belong in the witness, which `witness` checks). --legacy (packages not yet migrated)
#       turns a missing witness, a declaration and a non-False goal into WARN lines; every other rule holds.
# Every refusal prints the offending path or line and exits 1.
set -euo pipefail

ere_escape() { sed 's/[][\.*^$+?(){}|/]/\\&/g' <<<"$1"; }

cmd="${1:-}"; shift || true
case "$cmd" in
  shadow)
    [ "$#" -ge 3 ] || { echo "usage: lake_guard.sh shadow LEAN_PATH ROOT_LIB_DIR ROOT..." >&2; exit 2; }
    lean_path="$1"; root_lib="$(realpath -m "$2")"; shift 2
    bad=0
    IFS=':' read -r -a entries <<<"$lean_path"
    for e in "${entries[@]}"; do
      [ -n "$e" ] || continue
      [ "$(realpath -m "$e")" = "$root_lib" ] && continue
      for r in "$@"; do
        rp="${r//.//}"
        for cand in "$e/$rp" "$e/$rp.olean" "$e/$rp.ilean"; do
          if [ -e "$cand" ]; then
            echo "lean-path shadow: $cand shadows root library $r (LEAN_PATH entry $e precedes $root_lib)" >&2
            bad=1
          fi
        done
      done
    done
    [ "$bad" -eq 0 ] || exit 1
    echo "lean-path shadow check: PASS (${#entries[@]} entries, roots: $*)"
    ;;
  fresh)
    [ "$#" -ge 2 ] || { echo "usage: lake_guard.sh fresh BUILD_LOG ROOT..." >&2; exit 2; }
    python3 "$(dirname "$0")/fresh_build.py" "$@"
    ;;
  lean-error)
    [ "$#" -eq 2 ] || { echo "usage: lake_guard.sh lean-error LOG PATTERN" >&2; exit 2; }
    grep -q -E "^(.*:[0-9]+:[0-9]+: )?error(\([^)]*\))?: .*($2)" "$1"
    ;;
  witness|negative-control)
    command -v python3 > /dev/null || { echo "lake_guard.sh $cmd: python3 not found" >&2; exit 2; }
    python3 - "$cmd" "$@" <<'PY'
import re
import sys

ANSI = re.compile(r"\x1b\[[0-9;]*m")
SEV = r"(?P<sev>error|warning|info)(?:\([^)\s]*\))?"
LEAN_HDR = re.compile(r"^(?P<pos>\S.*?:\d+:\d+): " + SEV + r": ?(?P<msg>.*)$")    # lean FILE
LAKE_HDR = re.compile(r"^" + SEV + r": (?:(?P<pos>\S.*?:\d+:\d+): )?(?P<msg>.*)$")  # Lake replay / summary
JOB = re.compile(r"^(?P<mark>[\u2714\u2716\u26a0]) \[\d+/\d+\] ")                        # ✔ ✖ ⚠ [n/m]
LAKE_OTHER = re.compile(r"^(trace: |Some required targets logged failures:$|- \S+$|Build completed )")
SORRY_WARN = re.compile(r"declaration uses [`']sorry[`']")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\b")


def parse(path):
    """Diagnostics as (sev, pos, lines); Lake job marks; unrecognised lines outside any diagnostic."""
    diags, jobs, stray, cur = [], [], [], None
    with open(path, encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = ANSI.sub("", raw.rstrip("\n"))
            m = LEAN_HDR.match(line) or LAKE_HDR.match(line)
            if m:
                cur = (m.group("sev"), m.group("pos") or "", [m.group("msg")])
                diags.append(cur)
                continue
            j = JOB.match(line)
            if j or LAKE_OTHER.match(line):
                cur = None
                if j:
                    jobs.append(line)
                continue
            if cur is not None:
                cur[2].append(line)
            elif line.strip():
                stray.append(line)
    for _, _, lines in diags:
        while lines and not lines[-1].strip():
            lines.pop()
    return diags, jobs, stray


def strip_comments(text):
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def source_refusals(src):
    with open(src, encoding="utf-8", errors="replace") as fh:
        code = strip_comments(fh.read())
    bad = sorted(set(re.findall(r"(?<![\w.'])(sorry|admit|axiom)(?![\w'])", code)))
    return code, ["source uses `%s`" % w for w in bad]


def where(d):
    return d[1] or "(no position)"


def main(argv):
    mode, args = argv[0], argv[1:]
    legacy = mode == "negative-control" and args[:1] == ["--legacy"]
    if legacy:
        args = args[1:]
    if (mode == "witness" and len(args) != 3) or (mode != "witness" and len(args) not in (3, 4)):
        print("usage: lake_guard.sh witness SRC LOG EXIT | negative-control [--legacy] SRC LOG EXIT [WITNESS_MODULE]",
              file=sys.stderr)
        return 2
    src, log, code = args[0], args[1], args[2]
    witness = args[3] if len(args) == 4 else ""
    diags, jobs, stray = parse(log)
    src_text, refuse = source_refusals(src)
    warn = []
    errors = [d for d in diags if d[0] == "error"]
    for j in jobs:
        if j.startswith("\u2716"):
            refuse.append("Lake job failed: " + j)
    for s in stray[:5]:
        refuse.append("unrecognised output (not a Lean or Lake diagnostic): " + s)

    if mode == "witness":
        if code != "0":
            refuse.append("lake lean exited %s (a witness must compile: exit 0)" % code)
        for d in errors:
            refuse.append("error at %s: %s" % (where(d), d[2][0]))
        for d in diags:
            if d[0] == "warning" and SORRY_WARN.search(d[2][0]):
                refuse.append("sorry at %s: %s" % (where(d), d[2][0]))
        label = "negative-control witness"
    else:
        if code != "1":
            refuse.append("lake lean exited %s (a negative control must fail with exit 1)" % code)
        if not errors:
            refuse.append("no error diagnostic: the control was not rejected")
        goals = false_goals = 0
        for d in errors:
            head, body = d[2][0].strip(), d[2][1:]
            if head != "unsolved goals":
                refuse.append("extra error at %s (not unsolved goals): %s" % (where(d), " | ".join(d[2][:3])))
                continue
            blocks, block = [], []
            for line in body + [""]:
                if line.strip():
                    block.append(line)
                elif block:
                    blocks.append(block)
                    block = []
            if not blocks:
                refuse.append("unsolved goals at %s lists no goal" % where(d))
            for b in blocks:
                goals += 1
                if b[-1] == "\u22a2 False":
                    false_goals += 1
                else:
                    turn = [i for i, l in enumerate(b) if l.startswith("\u22a2")]
                    tail = " | ".join(b[turn[-1] if turn else -1:])
                    msg = "goal at %s does not end in exactly '\u22a2 False': %s" % (
                        where(d), tail[:200] + (" ..." if len(tail) > 200 else ""))
                    (warn if legacy else refuse).append(msg)
        if witness:
            imp = re.compile(r"^import\s+" + re.escape(witness) + r"\s*$", re.M)
            if not imp.search(src_text):
                refuse.append("control does not `import %s` (its witness)" % witness)
        else:
            (warn if legacy else refuse).append(
                "no witness: positive parts must be compiled separately (see the template README)")
        for line in src_text.splitlines():
            m = DECL.match(line.strip())
            if m:
                (warn if legacy else refuse).append(
                    "control declares `%s` (only `example`s; move positive helpers to the witness): %s"
                    % (m.group(1), line.strip()))
        label = "negative control" + (" (legacy)" if legacy else "")

    for w in warn:
        print("WARN %s %s: %s" % (label, src, w))
    if refuse:
        print("%s refused: %s" % (label, src), file=sys.stderr)
        for r in refuse:
            print("  - " + r, file=sys.stderr)
        return 1
    if mode == "witness":
        print("%s: PASS (%s compiles clean, %d warnings)" % (label, src,
              sum(1 for d in diags if d[0] == "warning")))
    else:
        print("%s: PASS (%s rejected only by unsolved goals: %d goal(s), %d ending in exactly \u22a2 False%s)" % (
            label, src, goals, false_goals, "; %d WARN" % len(warn) if warn else ""))
    return 0


sys.exit(main(sys.argv[1:]))
PY
    ;;
  *)
    echo "usage: lake_guard.sh shadow|fresh|lean-error|witness|negative-control ..." >&2; exit 2 ;;
esac
