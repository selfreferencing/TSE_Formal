# Epistemic finite extension: current statement ledger

Current checkpoint: compiled partial Waves 1, 1b and 2. All 14 mathematics modules
build together through `SEKernel.EpistemicFinite`. Part A and Part B still contain
explicit omissions. Wave 3 and optional analysis have not started.

## Result maps and status precedence

1. [Wave 1b current Part A additions and remaining gaps](STATEMENTS_EPISTEMIC_WAVE1B.md).
2. [Wave 2 current Part B mappings and remaining gaps](STATEMENTS_EPISTEMIC_WAVE2.md).
3. [Historical Wave 1 full inventory and notation ledger](STATEMENTS_EPISTEMIC_WAVE1.md).

The first two addenda supersede the historical ledger only for their named
results. Other Wave 1 statuses and its Wave 3 inventory remain in force.
Historical “not formalized” and “not started” text is not current evidence for a
result explicitly closed by a later addendum. Specifications' written proofs
are never counted as Lean compilation.

“Proved” means the described theorem compiled; “proved under an explicit
hypothesis” exposes the substantive model restriction. “Counterexample, algebra
only” is distinguished from a probability statement on an actual finite law.
“Not formalized” means no delivered theorem proves the specification result;
nearby definitions and ingredients do not close it.

## Verification

- [Combined build and audit command receipts](EpistemicReports/ThroughWave2/VERIFICATION.json).
- [Cold project build receipt](EpistemicReports/ThroughWave2/COLD_BUILD_RECEIPT.json).
- [All 383 named theorem declarations](EpistemicReports/ThroughWave2/THEOREMS.json).
- [Exact combined #print axioms output](EpistemicReports/ThroughWave2/AXIOMS.txt).
- [Axiom totals, protected-file checks and source hashes](EpistemicReports/ThroughWave2/AUDIT_SUMMARY.json).

All 19 original protected files and all six original Wave 1 mathematics sources
are unchanged. Only new source files plus the new extension umbrella/audit and
reports were added or updated. HEAD remains bd80f4a on chile-epistemic-evolution,
with no commits ahead of origin/main. Nothing was pushed; no PR or remote change
was made.
