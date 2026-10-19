# Print the fully qualified name of every public `theorem` or `lemma` in the given Lean files, tracking
# `namespace X` / `end X` blocks. Skips `private` declarations, `--` line comments and `/- ... -/` block
# comments, docstrings included (G7: lemmas were missed; G12: docstring prose such as "theorem derives ..."
# became an inventory entry). Attributes on the same line (`@[simp] theorem`) and `protected` are allowed.
# The source inventory is a cross-check only: owned_audit.sh audits every compiled constant.
FNR == 1 { n = 0; depth = 0 }
{
  line = $0
  # Strip block comments, which may nest and span lines.
  out = ""
  while (length(line) > 0) {
    if (depth > 0) {
      i = index(line, "-/"); j = index(line, "/-")
      if (j > 0 && (i == 0 || j < i)) { depth++; line = substr(line, j + 2); continue }
      if (i == 0) { line = ""; break }
      depth--; line = substr(line, i + 2); continue
    }
    j = index(line, "/-")
    if (j == 0) { out = out line; break }
    out = out substr(line, 1, j - 1); depth++; line = substr(line, j + 2)
  }
  sub(/--.*$/, "", out)
  if (out ~ /^namespace [A-Za-z0-9_.']+/) { split(out, w, /[ \t]+/); n++; ns[n] = w[2]; next }
  if (out ~ /^end [A-Za-z0-9_.']+/) { split(out, w, /[ \t]+/); if (n > 0 && ns[n] == w[2]) n--; next }
  s = out
  sub(/^@\[[^]]*\][ \t]*/, "", s)
  sub(/^protected[ \t]+/, "", s)
  if (s ~ /^(theorem|lemma)[ \t]+[A-Za-z0-9_.']+/) {
    split(s, w, /[ \t]+/); name = w[2]; prefix = ""
    for (k = 1; k <= n; k++) prefix = prefix ns[k] "."
    print prefix name
  }
}
