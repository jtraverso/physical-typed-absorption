# Triangle decompositions III in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

The Lean source supplement of *Triangle decompositions III: Physical typed absorption and
prescribed statistics*, preprint 1.0, 1 November 2026
([doi:10.5281/zenodo.23867836](https://doi.org/10.5281/zenodo.23867836)), packaged for the
Palomar registry. The manuscript and the original archive
`archives/PAPER_III_LEAN_SOURCE_v1.0.zip` are public in
[jtraverso/nash-williams-triangle-decompositions-release](https://github.com/jtraverso/nash-williams-triangle-decompositions-release).

| Lean | Manuscript |
|---|---|
| `TypedTriangle.Vortex.main_theorem_T` | **Theorem T.** H1–H4 imply an allowed triangle decomposition of every sufficiently large labelled graph. |
| `TypedTriangle.Vortex.main_theorem_T_with_triangle_monitors_and_pasch` | **Theorem T+.** The decomposition can also follow at most `n^q` bounded triangle tests and the Pasch count of the seed, up to `η n²`. |
| `TypedTriangle.Applications.Latin.latin_square_with_profile_statistics` | **Theorem 8.1.** Latin squares with a bounded stochastic profile, prescribed statistics and Pasch count. |
| `TypedTriangle.Applications.Latin.uniform_with_intercalates` | **Corollary 8.2.** The uniform profile, with about `(m−1)³/(4m)` intercalates. |
| `TypedTriangle.Applications.Latin.signed_profile_with_intercalates` | **Corollary 8.3.** Signed rank-one profiles and their intercalate targets. |
| `TypedTriangle.Applications.Latin.TwoScale.latin_two_scale_with_blocks` | **Theorem 8.4.** Two Latin squares with the same statistics and coarse blocks and intercalate counts near `κ(θ,0) m²` and `κ(θ,t) m²`. |
| `TypedTriangle.Applications.FivePartite.main_theorem` | **Corollary 8.5.** Rainbow decompositions of `K_{s,s,s,s,s}` (`s = 3|A|`) with prescribed statistics and Pasch count. |

## The hypotheses of Theorem T

A *host* is a finite simple graph with a vertex labelling `lab : V → I`; a triangle is *allowed*
when its label multiset lies in `F`. With `n = |V|`:

- **H1** (`IsDiffuseSeed`): weights `μ` on allowed triangles with `1/(Cn) ≤ μ ≤ C/n` that sum to
  one on every edge;
- **H2** (`IsPhysical`): the edge indicator lies in the integer span of the indicators of the
  allowed triangles;
- **H3** (`CommonNbrCond`): every pair of distinct vertices has at least `α n` common neighbours
  of each label completing an allowed type;
- **H4** (`HingeCond`): every two allowed triangles on a common edge have at least `α n^(i−4)`
  physical hinges of some order `6 ≤ i ≤ h`.

All thresholds are existential. The criterion is a variant of the partitioned framework of
Delcourt and Postle (arXiv:2606.11178, Section 13.2): H3 is their anti-edgeful condition and the
hinge is their Definition 13.14, while H1 and H2 are stronger than their hypotheses. Their
Theorem 13.16 is neither imported nor assumed.

## Files

- [`PaperIIIChallenge.lean`](PaperIIIChallenge.lean): the definitions and the seven statements.
  It imports only Mathlib; every definition is copied verbatim, with its options and `open`
  declarations, from the source file named above it.
- [`PaperIIISolution.lean`](PaperIIISolution.lean): imports the six endpoint modules of the
  source supplement, which contain the seven theorems under the same names.
- `RequestProject/`, `PartitionedTriangleAbsorption/`, `PartitionedTriangleAbsorption.lean`,
  `audit/`: the source supplement, **byte-identical** to the published archive (1,141 project
  modules, including the vendored sources of Papers I–II and of Ehard–Glock–Joos).
- `supplement/`: the archive's own `README.md`, `lakefile.toml`, `SHA256SUMS.txt`,
  `source_closure.json` and `verify_sha256.py`, and its `audit/closure-audit.lean` (a
  `#print axioms` script outside the module system) as `closure-audit.lean.txt`. Only the
  top-level `lakefile.toml` differs from the archive: it adds the Challenge and Solution
  libraries, raises `maxHeartbeats` to 1,600,000 and includes the root module
  `PartitionedTriangleAbsorption` in its library (the glob `.*` instead of `.+`), because the
  archive was assembled with validated object reuse and a build from an empty cache exceeds the
  default limit in some modules and needs that root (imported by `Stage2`). `lake-manifest.json`,
  `lean-toolchain` and `LICENSE` are unchanged. `python verify_supplement.py` checks every file
  of the archive's SHA-256 list against this repository.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## Not compared

The explicit tower threshold of Theorem 7.2 (`MainPaperIIITriangleTower`,
`PaperIIIHeightProgram`) is proved in the sources but not compared: its threshold is a
two-thousand-line integer program. For Theorem 8.4, the exact finite identity (8.23) of the
manuscript is a written calculation; the Lean endpoint uses the estimate (8.24).

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

The archive records 1,141 project compilations and six endpoint axiom audits (`audit/`): only
`propext`, `Classical.choice` and `Quot.sound` occur. The Challenge compiles against Mathlib alone.

The Lean development was produced with AI assistance under the author's direction (see
`formalization.yaml`). No independent human review of the formalization is claimed.
