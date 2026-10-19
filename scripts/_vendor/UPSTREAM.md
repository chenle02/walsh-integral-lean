# lean-pkg build-log parser

lean_pkg_lake_hygiene.py is a byte-exact copy of lean_pkg/lake_hygiene.py from lean-pkg 0.18.0, https://github.com/lean-pkg/lean-pkg. Apache-2.0 LICENSE is retained here. The library's fresh_build.py calls its actual build_section, job_lines and cache_reuse_problems functions and additionally requires every expected own module to have a Built action.

A warning replay after an earlier Built for the same module in the same log is allowed by upstream; cache restoration before any Built remains refused. The raw build window must retain all actions without filtering away own cache hits.
