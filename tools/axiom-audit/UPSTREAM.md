# Audit tool provenance

The environment loader and shared collector in AxiomAudit.lean are from leanprover-community/axiom-audit, commit 46024e005996495c65ef609368e11ab39c4222e3 (v0.1.2), under Apache-2.0; LICENSE is retained unchanged. AxiomAudit.lean is unchanged from that source.

Main.lean is a local driver selecting exact compiled module ownership, including private/generated declarations, and serializing kernel Expr types. Its neutral JSON schema is lean-library-native-owned-audit/1. This driver does not kernel-replay proofs: imported environments use high trust only for inspection, paired with a separate whole-module leanchecker replay.

The shared collector reports the complete projectwide forbidden-axiom union for axiom-clean imports. Per-declaration lists may undercount cyclic dependency clusters; they are not advertised as canonical per-theorem fingerprints. Preserve this limitation when interpreting the report.
