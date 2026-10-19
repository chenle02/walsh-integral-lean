# Supplementary native audit evidence

The compressed files contain complete native declaration reports from the actual cold run named in summary.json: exact declaration names, owning modules, serialized elaborated types and axiom dependencies. Decompress with gzip -dc and verify the uncompressed byte count and SHA-256 in summary.json. The original deterministic gzip bytes and compressed digests are preserved.

These files supplement the canonical receipt and its sealed redacted log. They are not replacement receipts, reusable theorem claim slots or an independent comparator certificate. Public summaries intentionally omit absolute provider paths, raw machine identifiers and negative-compiler diagnostics; those exact run bindings remain in private retained evidence. This does not weaken the published complete native declaration reports.

The global forbidden-axiom union is the ownership audit decision. Individual cached dependency lists can undercount cyclic clusters and must not be treated as unique axiom fingerprints. LeanChecker uses the pinned Lean implementation; independent comparator evidence is separately named in canonical records. Source hypotheses and quantifiers remain authoritative.
