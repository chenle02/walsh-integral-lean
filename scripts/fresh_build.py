"""Fresh own-module build guard using lean-pkg's exact upstream cache semantics."""
from pathlib import Path
import sys
from _vendor.lean_pkg_lake_hygiene import build_section, job_lines, cache_reuse_problems

def expected_modules(project, roots):
    paths=[]
    for root in roots:
        head=project/(root.replace('.','/')+'.lean')
        if head.is_file():paths.append(head)
        sub=project/root.replace('.','/')
        if sub.is_dir():paths.extend(sorted(sub.rglob('*.lean')))
    return {str(p.relative_to(project).with_suffix('')).replace('/','.') for p in paths}

def check(text, expected, roots):
    lean_files=[m.replace('.','/')+'.lean' for m in expected]
    refusals, checks=cache_reuse_problems(text,lean_files,set(roots))
    jobs=job_lines(build_section(text))
    built={target for verb,target in jobs if verb=='Built'}
    missing=sorted(expected-built)
    if missing:refusals.append('Expected own modules not Built: '+', '.join(missing))
    if not expected:refusals.append('No expected own source modules')
    return refusals, checks

def main():
    log=Path(sys.argv[1]);roots=sys.argv[2:]
    expected=expected_modules(Path.cwd(),roots)
    refusals,_=check(log.read_text(),expected,roots)
    if refusals:
        for row in refusals:print('fresh build check: '+row,file=sys.stderr)
        return 1
    print(f'fresh build check: PASS ({len(expected)} exact own modules Built; later dependency warning replay allowed only after same-module Built)')
    return 0
if __name__=='__main__':raise SystemExit(main())
