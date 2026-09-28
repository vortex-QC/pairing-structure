/- Pairing-structure minimal build root.
   Imports exactly the 20 files listed in Appendix A of the paper so that
   `lake build` reproduces the zero-sorry claims (195 items, Appendix-A accounting)
   without the full 42-file library. Full library: density-math (in-framework).
   Toolchain: leanprover/lean4:v4.33.1 with Mathlib v4.33.1 (pinned in lakefile.toml). -/
import Mathlib
import DensityMath.DualityPairing
import DensityMath.DualityPairingDeep
import DensityMath.DualityPinning
import DensityMath.DualityNet
import DensityMath.DualityIdem
import DensityMath.ConfirmProj
import DensityMath.ConfirmProjPair
import DensityMath.ConfirmProjHilbert
import DensityMath.ConfirmProjQuad
import DensityMath.ConfirmProjSpectral
import DensityMath.ConfirmProjFamily
import DensityMath.ConfirmProjFubini
import DensityMath.ConfirmProjContSpec
import DensityMath.EBKQuantization
import DensityMath.DualityRatio
import DensityMath.DualityRG
import DensityMath.DualityConvention
import DensityMath.DualitySandwich
import DensityMath.DualityLambda
import DensityMath.ObservationDims
