# Weil Representation over Finite Fields

A Lean 4 research project on Heisenberg groups, Schrödinger models, pseudosymplectic groups, and Weil operators over finite fields, with computations in characteristic two.

Repository: [lizhe0828/weil-representation](https://gitee.com/lizhe0828/weil-representation).

Clone URL: `https://gitee.com/lizhe0828/weil-representation.git`; default branch: `master`.

See [README.md](README.md) for the full Chinese guide, module map, and migration details.

**This is an unfinished research project. It contains `sorry`, `native_decide`, and `#eval!`. A successful build does not certify that all mathematical claims have complete proofs.** The reorganization preserves the existing definitions and proof progress; it does not complete the Weil representation or the double cover.

## Build

The project keeps Lean `v4.15.0-rc1` and mathlib commit `b2158cc40abd16b858e8aa3b0e6f452789b4b28b`, pinned in both the Lake configuration and manifest. No dependency upgrade is part of this cleanup.

```sh
git clone https://gitee.com/lizhe0828/weil-representation.git
cd weil-representation
lake exe cache get
./scripts/check.sh
```

Open the directory in VS Code with the `leanprover.lean4` extension. The library entry point is [WeilRepFinitefield.lean](WeilRepFinitefield.lean).

`lake build` checks the main library. The script also builds the two independent computational examples:

```sh
lake build WeilRepFinitefield.Examples.F2 WeilRepFinitefield.Examples.Cocycle
```

The examples retain their own global notation and must be imported separately. They and the preserved library demonstrations print computational results. In particular, `#eval!` output is not a replacement for completing the outstanding proofs. Files in `archive/` are not included in these checks.

## Organization and migration

- Main chain: `Compute → Heisenberg / QuadForm2 → HeisenbergRepresentation / PseudoSymplecticGroup → WeilRep`.
- `HeisenbergRepresentation` now contains both the Schrödinger function space and its representation. Replace direct imports of the former `SchrodingerModel` module with this module; the `Schrodinger_Model` namespace is retained.
- The forwarding `Basic` module is removed; use `import WeilRepFinitefield` instead.
- `F2` moves to `WeilRepFinitefield.Examples.F2`; the newer upstream `F2_example` moves to `WeilRepFinitefield.Examples.Cocycle`.
- `QuadraticRing` and `Quadratictwo` provide the exact coefficient field used by the examples.
- Five historical implementations and the original local example are preserved in [archive/](archive/README.md), outside the current library. These drafts are not claimed to compile independently.

The integration starts from upstream `86652e985c97a0000156262c57fc37a13226835c`, preserving its two commits after the original local `76ea196`. The local cocycle edit is already present upstream. The conflicting older local example is preserved verbatim as `archive/F2_example_local.lean`; the active example uses the newer upstream implementation. Other local source edits remain in the corresponding active or archived files.

Outstanding work includes the quadratic-form encoding equivalence, parts of the Y-model equivalence and action formulas, pseudosymplectic composition, the intertwining construction, and example polarizations and character extensions. `DPs` currently has data and a candidate multiplication, not a completed double-cover group construction. No new mathematical axioms or placeholders were introduced by this reorganization; existing unfinished proofs remain visible.

## Synchronization and review

Preserve uncommitted work before updating. On `master`, use `git pull --ff-only origin master`, run the checks, and commit and push deliberate changes. After `git fetch origin`, `git rev-list --left-right --count HEAD...origin/master` should return `0 0` and `git status --short` should be empty to confirm synchronization with the fetched remote state. This is a point-in-time check; automatic pushing is not configured.

The independent [review report](REVIEW.md) and [source manifest](docs/REVIEW_TARGET.sha256) cover this integration and reorganization, not completion of the existing mathematical gaps. Dependency caches, generated build artifacts, logs, and `.DS_Store` are excluded from Git.
