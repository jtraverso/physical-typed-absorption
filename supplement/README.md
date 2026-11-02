# Paper III — formal source supplement, preprint 1.0

This supplement contains 1,141 project modules for Triangle decompositions III:
Physical typed absorption and prescribed statistics, and the eight explicit
targets below. The complete general proofs are supplied in Lean. The manuscript
explains their construction and gives the application proofs.

Lean: 4.35.0-rc3. Mathlib: c55e6e786f49471c72fbddbec5415808896aec1e.
The accompanying verification records 1,141 successful project compilations.
Fifteen documentation-only source changes were checked to leave all text outside
Lean comments identical and those fifteen modules were recompiled. The other
1,126 modules were reused after source and object hash validation. Six endpoint
axiom queries were then rerun successfully, using fully qualified axiom names.
Only propext, Classical.choice and Quot.sound occur. This is a reconstruction
with validated reuse, not an uninterrupted build from an empty cache.

## Verify and reproduce

Run `python verify_sha256.py` from this directory. Install the pinned toolchain
and dependencies in lake-manifest.json; do not run `lake update`. External
dependencies and compiled objects are not included in this source supplement.

```
lake build RequestProject.TypedTriangle.MainPaperIII
lake build RequestProject.TypedTriangle.MainPaperIIIPasch
lake build RequestProject.TypedTriangle.MainPaperIIITriangleTower
lake build RequestProject.TypedTriangle.ApplicationsLatinMain
lake build RequestProject.TypedTriangle.ApplicationsLatinCorollaries
lake build RequestProject.TypedTriangle.ApplicationsFivePartiteMain
lake build RequestProject.TypedTriangle.ApplicationsTwoScaleFinal
lake build RequestProject.TypedTriangle.PaperIIIHeightProgram
```

The default Lake target is MainPaperIII only. The other listed targets are
separate entries. The two-scale Latin application is assembled in
ApplicationsTwoScaleFinal.lean; the exact finite inclusion–exclusion identity
in manuscript equation (8.23) remains a written calculation, distinct from the
formal diagonal estimate used by that endpoint.

After building, run each file in audit/ separately, for example:

```
lake env lean -Dpp.fullNames=true audit/main-paper-iii-audit.lean
```

The six query files may use separate compatible import closures. Their reports
are in audit/VERIFICATION.json and audit/logs/. source_closure.json lists all
project sources. Comment-equivalence and source/object bindings accompany the
internal evidence. A fresh independent rebuild can be performed with the commands
above; the recorded audit does not claim to have rebuilt external dependencies.
