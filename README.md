# pairing-structure

Replication package for the paper:

**配对结构：确认动作与约束读出的公理化构造 / The Pairing Structure: An Axiomatic Construction of Confirming Actions and Constraint Readouts**

- Paper (CN + EN): DOI [10.5281/zenodo.23013940](https://doi.org/10.5281/zenodo.23013940) (concept 10.5281/zenodo.23013939)

## What is formalized

The binding between a confirming action and a constraint readout (the Pairing: an idempotent
confirming action f x a discrete constraint readout r), as the axiom form of the measurement
postulate's specialization family (third member). Load-bearing mappings: pairing core (7) →
deep pairing theorems (12) → projection-assumption eight blocks (53) → EBK quantization (10) →
meta-constraint rows (45). **All 195 items zero sorry (20 files, Appendix-A accounting).**

## Files (paper Appendix A, 20 files)

| File | Items | Layer |
|---|---|---|
| DualityPairing.lean | 7 | pairing core |
| DualityPairingDeep.lean | 12 | deep theorems (idempotent dynamics classification, readout-collapse exclusivity) |
| DualityPinning.lean | 5 (incl. ChainTwo 2) | two-point pinning core |
| DualityNet.lean | 25 | observation network (order-structure face) |
| DualityIdem.lean | 4 | idempotent family |
| ConfirmProj.lean | 6 | projection kernel |
| ConfirmProjPair.lean | 7 | commutation two faces |
| ConfirmProjHilbert.lean | 5 | spectral block |
| ConfirmProjQuad.lean | 11 | joint spectrum, general n |
| ConfirmProjSpectral.lean | 16 | spectral measure |
| ConfirmProjFamily.lean | 8 | family |
| ConfirmProjFubini.lean | 3 | Fubini normalization |
| ConfirmProjContSpec.lean | 11 | continuous spectrum ProjVM (no-atom finite collapse) |
| EBKQuantization.lean | 10 | EBK (pi/hbar division of labor) |
| DualityRatio.lean | 4 | readout ratio |
| DualityRG.lean | 7 (+ gamma 5) | renormalization-flow reading |
| DualityConvention.lean | 4 | convention row |
| DualitySandwich.lean | 6 | sandwich |
| DualityLambda.lean | 25 | pure-anchor band (1,323-monomial zero hits) |
| ObservationDims.lean | 6 | dimension instantiation |

**Verified claim**: `lake build` on this trimmed root passes with **zero sorry** across all
20 files; `#print axioms` within {propext, Classical.choice, Quot.sound} (several files use
zero axioms). Note: Appendix-A counts use the paper's proposition-item accounting; raw
`grep '^theorem'` declaration counts differ for some files (e.g. DualityNet: 32 declarations)
— the build-level claim is the reproducible one.

## How to reproduce

```bash
cd lean
lake build        # Lean prover v4.33.1, Mathlib v4.33.1 (pinned)
```

## License

Code (`lean/`): MIT. This README: CC-BY-4.0.
