/-
  TDLean.Audit -- the enforced axiom roll-call.

  Each block below asserts, at build time, that a headline theorem sits at tier L1:
  axioms exactly `[propext, Classical.choice, Quot.sound]`, and in particular NOT
  `sorryAx`. `#guard_msgs` turns `#print axioms` from a printout into an assertion --
  strictly stronger than the Coq side's trailing `Print Assumptions`, which only prints.

  Because TDLean.lean imports this file last, a green `lake build TDLean` IS the audit.

  Add one block per headline as bricks land. See LEDGER.md section 2 for the tier table,
  and in particular for why tier L1 -- not "axiom-free" -- is the honest bar in Lean.
-/
import TDLean.Basic
import TDLean.MonoidAlgebra.ZMod.PrimeIsWithZero
import TDLean.MonoidAlgebra.Sym.SignType
import TDLean.MonoidAlgebra.PrimorialLimit
import TDLean.Newman.Region
import TDLean.Newman.Kernel
import TDLean.Newman.Contour
import TDLean.Newman.Winding
import TDLean.Newman.StarPrimitive
import TDLean.Newman.TruncCauchy
import TDLean.Newman.Laplace
import TDLean.Newman.Split
import TDLean.Newman.LeftLimit
import TDLean.Zeta.Basic
import TDLean.Zeta.Continuation
import TDLean.Zeta.Holo
import TDLean.Zeta.Telescope
import TDLean.Zeta.LogDeriv
import TDLean.Zeta.DirichletMul
import TDLean.Zeta.VonMangoldt
import TDLean.Zeta.Identity
import TDLean.Zeta.RayIdentity
import TDLean.Zeta.Conj
import TDLean.Zeta.CriticalLine
import TDLean.Zeta.Mertens
import TDLean.Zeta.LogDerivOrder
import TDLean.Zeta.NonVanishing
import TDLean.Zeta.PhiHolo
import TDLean.PNT.Chebyshev
import TDLean.PNT.Mellin
import TDLean.PNT.Substitution
import TDLean.PNT.NewmanInput
import TDLean.PNT.GNewman
import TDLean.PNT.Region
import TDLean.PNT.Tauberian
import TDLean.PNT.Squeeze
import TDLean.PNT.Transfer
import TDLean.PNT.PiCount
import TDLean.PNT.PrimeCountingAsymp
import TDLean.FE.Theta.Transform
import TDLean.FE.Mellin.Term
import TDLean.FE.Mellin.Completed
import TDLean.Operator.Ell2C
import TDLean.Operator.Number
import TDLean.Operator.Isometry
import TDLean.Operator.BCAlgebra
import TDLean.Operator.QModZ
import TDLean.Operator.Rep
import TDLean.Operator.RootSum
import TDLean.Newman.Tauberian
import TDLean.FE.Mellin.Split
import TDLean.FE.Mellin.FunctionalEquation
import TDLean.FE.Strip
import TDLean.FE.Holo
import TDLean.FE.Transfer
import TDLean.FE.Continuation
import TDLean.FE.Classical
import TDLean.FE.CriticalValue
import TDLean.FE.Xi
import TDLean.FE.Growth
import TDLean.FE.CriticalFormula

/-! ### Cluster B -- monoid algebra of prime length -/

/-- info: 'TDLean.MonoidAlgebra.card_withZero_units' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.card_withZero_units

/-- info: 'TDLean.MonoidAlgebra.card_units_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.card_units_eq

/-- info: 'TDLean.MonoidAlgebra.symVal_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.symVal_injective

/-- info: 'TDLean.MonoidAlgebra.symVal_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.symVal_mul

/-- info: 'TDLean.MonoidAlgebra.card_signType' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.card_signType

/-! ### Cluster C -- Newman contour route -/

/-- info: 'TDLean.Newman.convex_truncDisk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.convex_truncDisk

/-- info: 'TDLean.Newman.isOpen_truncDisk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.isOpen_truncDisk

/-- info: 'TDLean.Newman.newmanKernel_of_norm_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newmanKernel_of_norm_eq

/-- info: 'TDLean.Newman.norm_newmanKernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_newmanKernel

/-- info: 'TDLean.Newman.truncContour_eq_zero_of_primitive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncContour_eq_zero_of_primitive

/-- info: 'TDLean.Newman.arcIntegral_eq_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.arcIntegral_eq_sub

/-- info: 'TDLean.Newman.chordIntegral_eq_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.chordIntegral_eq_sub

/-- info: 'TDLean.Newman.hasDerivAt_comp_ofReal_path' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.hasDerivAt_comp_ofReal_path

/-- info: 'TDLean.Newman.trunc_winding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.trunc_winding

/-- info: 'TDLean.Newman.arcIntegral_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.arcIntegral_inv

/-- info: 'TDLean.Newman.chordIntegral_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.chordIntegral_inv

/-- info: 'TDLean.Newman.hasDerivAt_logNeg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.hasDerivAt_logNeg

/-- info: 'TDLean.Newman.hasDerivAt_radialIntegrand' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.hasDerivAt_radialIntegrand

/-- info: 'TDLean.Newman.hasDerivAt_radialAntiderivative' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.hasDerivAt_radialAntiderivative

/-- info: 'TDLean.Newman.radialCone_subset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.radialCone_subset

/-- info: 'TDLean.Newman.hasDerivAt_radialPrimitive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.hasDerivAt_radialPrimitive

/-- info: 'TDLean.Newman.truncContour_eq_zero_of_starAboutZero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncContour_eq_zero_of_starAboutZero

/-- info: 'TDLean.Newman.starAboutZero_truncDisk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.starAboutZero_truncDisk

/-- info: 'TDLean.Newman.trunc_cauchy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.trunc_cauchy

/-- info: 'TDLean.Newman.div_eq_dslope_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.div_eq_dslope_add

/-- info: 'TDLean.Newman.truncContour_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncContour_add

/-- info: 'TDLean.Newman.truncContour_const_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncContour_const_mul

/-- info: 'TDLean.Newman.hasDerivAt_gT' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.hasDerivAt_gT

/-- info: 'TDLean.Newman.differentiable_gT' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.differentiable_gT

/-- info: 'TDLean.Newman.norm_laplaceTail_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_laplaceTail_le

/-- info: 'TDLean.Newman.newman_contour_identity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newman_contour_identity

/-- info: 'TDLean.Newman.truncContour_kernelPoly_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncContour_kernelPoly_eq_zero

/-- info: 'TDLean.Newman.norm_newman_integrand_right' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_newman_integrand_right

/-- info: 'TDLean.Newman.norm_arcIntegral_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_arcIntegral_le

/-- info: 'TDLean.Newman.norm_chordIntegral_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_chordIntegral_le

/-- info: 'TDLean.Newman.truncContour_split' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncContour_split

/-- info: 'TDLean.Newman.leftPart_eq_of_truncContour_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.leftPart_eq_of_truncContour_eq

/-- info: 'TDLean.Newman.leftPart_kernel_deform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.leftPart_kernel_deform

/-- info: 'TDLean.Newman.norm_arcIntegralOn_le_of_ae' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_arcIntegralOn_le_of_ae

/-- info: 'TDLean.Newman.norm_newman_integrand_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_newman_integrand_left

/-- info: 'TDLean.Newman.norm_gT_le_of_re_neg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_gT_le_of_re_neg

/-- info: 'TDLean.Newman.integral_exp_mul_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.integral_exp_mul_zero

/-- info: 'TDLean.Newman.norm_rightSemi_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_rightSemi_le

/-- info: 'TDLean.Newman.norm_leftArc_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_leftArc_le

/-- info: 'TDLean.Newman.newman_tauberian' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newman_tauberian

/-- info: 'TDLean.Newman.newman_inequality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newman_inequality

/-- info: 'TDLean.Newman.tendsto_leftPart_g_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.tendsto_leftPart_g_zero

/-- info: 'TDLean.Newman.norm_leftPart_pi_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_leftPart_pi_le

/-- info: 'TDLean.Newman.leftPart_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.leftPart_sub

/-- info: 'TDLean.Newman.sub_gT_eq_tail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.sub_gT_eq_tail

/-- info: 'TDLean.MonoidAlgebra.squarefree_prod_primes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.squarefree_prod_primes

/-- info: 'TDLean.MonoidAlgebra.toZMod_not_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.toZMod_not_injective

/-- info: 'TDLean.MonoidAlgebra.pairwise_coprime_primes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.pairwise_coprime_primes

/-- info: 'TDLean.MonoidAlgebra.primorial_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.primorial_nonvacuous

/-! ### Cluster C9 -- zeta from scratch -/

/-- info: 'TDLean.Zeta.norm_cpow_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.norm_cpow_sub_le

/-- info: 'TDLean.Zeta.summable_zetaTerm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.summable_zetaTerm

/-- info: 'TDLean.Zeta.hasDerivAt_cpow_neg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.hasDerivAt_cpow_neg

/-- info: 'TDLean.Zeta.norm_zetaDiff_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.norm_zetaDiff_le

/-- info: 'TDLean.Zeta.summable_zetaDiff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.summable_zetaDiff

/-- info: 'TDLean.Zeta.zetaDiff_eq_integral' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaDiff_eq_integral

/-- info: 'TDLean.Zeta.differentiableOn_zetaDiffSum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.differentiableOn_zetaDiffSum

/-- info: 'TDLean.Zeta.differentiableAt_zetaDiff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.differentiableAt_zetaDiff

/-- info: 'TDLean.Zeta.hasDerivAt_intCpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.hasDerivAt_intCpow

/-- info: 'TDLean.Zeta.zetaCont_eq_zetaSeries' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_eq_zetaSeries

/-- info: 'TDLean.Zeta.differentiableAt_zetaCont' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.differentiableAt_zetaCont

/-- info: 'TDLean.Zeta.zetaDiffSum_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaDiffSum_eq

/-- info: 'TDLean.Zeta.intCpow_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.intCpow_eq

/-- info: 'TDLean.Zeta.hasSum_deriv_zetaSeries' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.hasSum_deriv_zetaSeries

/-- info: 'TDLean.Zeta.hasDerivAt_zetaTerm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.hasDerivAt_zetaTerm

/-- info: 'TDLean.Zeta.LS_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.LS_mul

/-- info: 'TDLean.Zeta.term_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.term_mul

/-- info: 'TDLean.Zeta.dconv_muC_zetaC' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.dconv_muC_zetaC

/-- info: 'TDLean.Zeta.LS_eq_tsum_nat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.LS_eq_tsum_nat

/-- info: 'TDLean.Zeta.LS_one_eq_zetaSeries' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.LS_one_eq_zetaSeries

/-- info: 'TDLean.Zeta.LS_delta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.LS_delta

/-- info: 'TDLean.Zeta.eqOn_halfplane_of_eqOn_subhalfplane' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.eqOn_halfplane_of_eqOn_subhalfplane

/-- info: 'TDLean.Zeta.zetaDiffSum_unique' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaDiffSum_unique

/-- info: 'TDLean.Zeta.deriv_zetaCont_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.deriv_zetaCont_eq

/-- info: 'TDLean.Zeta.eqOn_of_eventuallyEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.eqOn_of_eventuallyEq

/-- info: 'TDLean.Zeta.LS_vonMangoldt_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.LS_vonMangoldt_eq

/-- info: 'TDLean.Zeta.LS_vonMangoldt_mul_zeta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.LS_vonMangoldt_mul_zeta

/-- info: 'TDLean.Zeta.zetaSeries_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaSeries_ne_zero

/-- info: 'TDLean.Zeta.dconv_LamC_zetaC' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.dconv_LamC_zetaC

/-- info: 'TDLean.Zeta.summable_log_rpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.summable_log_rpow

/-! ### Non-vacuity witnesses

    These must be audited too. A `sorry` here is exactly as fatal as a `sorry` in a
    headline -- an unproved non-vacuity witness means the headline may be quantifying
    over an empty set, which `#print axioms` on the headline alone would not reveal.
    (Found by testing the gate: a `sorry` injected into an unlisted witness passed the
    build. See LEDGER.md section 2, item 2.) -/

/-- info: 'TDLean.MonoidAlgebra.zmodPrimeEquiv_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.zmodPrimeEquiv_nonvacuous

/-- info: 'TDLean.MonoidAlgebra.symVal_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.MonoidAlgebra.symVal_values

/-- info: 'TDLean.Newman.truncDisk_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.truncDisk_nonvacuous

/-- info: 'TDLean.Newman.zero_mem_truncDisk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.zero_mem_truncDisk

/-- info: 'TDLean.Newman.newmanKernel_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newmanKernel_nonvacuous

/-- info: 'TDLean.Newman.contourSet_nonempty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.contourSet_nonempty

/-- info: 'TDLean.Newman.trunc_winding_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.trunc_winding_nonvacuous

/-- info: 'TDLean.Newman.newman_tauberian_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.newman_tauberian_nonvacuous

/-- info: 'TDLean.Newman.norm_newman_integrand_right_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Newman.norm_newman_integrand_right_nonvacuous

/-! ### C9 item 3, phase 1: Mertens' inequality -/

/-- info: 'TDLean.Zeta.three_add_four_cos_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.three_add_four_cos_nonneg

/-- info: 'TDLean.Zeta.cpow_neg_re' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.cpow_neg_re

/-- info: 'TDLean.Zeta.re_LS_LamC' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.re_LS_LamC

/-- info: 'TDLean.Zeta.summable_mertensTerm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.summable_mertensTerm

/-- info: 'TDLean.Zeta.mertens_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.mertens_nonneg

/-- info: 'TDLean.Zeta.summable_mertensTerm_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.summable_mertensTerm_nonvacuous

/-! ### C9 item 3, phase 2: logarithmic derivative at a zero (absent from mathlib) -/

/-- info: 'TDLean.Zeta.logDeriv_sub_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.logDeriv_sub_pow

/-- info: 'TDLean.Zeta.logDeriv_eventuallyEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.logDeriv_eventuallyEq

/-- info: 'TDLean.Zeta.logDeriv_eq_order_div_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.logDeriv_eq_order_div_add

/-- info: 'TDLean.Zeta.tendsto_sub_mul_logDeriv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.tendsto_sub_mul_logDeriv

/-- info: 'TDLean.Zeta.logDeriv_sub_pow_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.logDeriv_sub_pow_nonvacuous

/-! ### C9 item 3: zeta has no zero on the line `Re s = 1` -/

/-- info: 'TDLean.Zeta.analyticAt_zetaCont' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.analyticAt_zetaCont

/-- info: 'TDLean.Zeta.zetaCont_eq_poleFactor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_eq_poleFactor

/-- info: 'TDLean.Zeta.analyticOrderAt_zetaCont_ne_top' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.analyticOrderAt_zetaCont_ne_top

/-- info: 'TDLean.Zeta.LS_LamC_eq_neg_logDeriv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.LS_LamC_eq_neg_logDeriv

/-- info: 'TDLean.Zeta.tendsto_mertensW' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.tendsto_mertensW

/-- info: 'TDLean.Zeta.tendsto_mertensW_pole' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.tendsto_mertensW_pole

/-- info: 'TDLean.Zeta.tendsto_mertensW_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.tendsto_mertensW_zero

/-- info: 'TDLean.Zeta.zetaCont_ne_zero_of_re_eq_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_ne_zero_of_re_eq_one

/-- info: 'TDLean.Zeta.zetaCont_ne_zero_of_one_le_re' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_ne_zero_of_one_le_re

/-- info: 'TDLean.Zeta.zetaCont_ne_zero_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_ne_zero_nonvacuous

/-! ### C9 item 4: the pole-subtracted logarithmic derivative -/

/-- info: 'TDLean.Zeta.zetaPoleFactor_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaPoleFactor_ne_zero

/-- info: 'TDLean.Zeta.logDeriv_zetaCont_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.logDeriv_zetaCont_eq

/-- info: 'TDLean.Zeta.PhiMinus_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.PhiMinus_eq

/-- info: 'TDLean.Zeta.isOpen_phiRegion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.isOpen_phiRegion

/-- info: 'TDLean.Zeta.halfplane_subset_phiRegion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.halfplane_subset_phiRegion

/-- info: 'TDLean.Zeta.differentiableOn_PhiMinus' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.differentiableOn_PhiMinus

/-- info: 'TDLean.Zeta.PhiMinus_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.PhiMinus_nonvacuous

/-! ### C10 part 1: Chebyshev theta (from scratch; mathlib's Chebyshev.lean is gate-banned) -/

/-- info: 'TDLean.PNT.theta_eq_log_primorial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.theta_eq_log_primorial

/-- info: 'TDLean.PNT.theta_le_mul_log4' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.theta_le_mul_log4

/-- info: 'TDLean.PNT.theta_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.theta_nonneg

/-- info: 'TDLean.PNT.psi_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psi_nonneg

/-- info: 'TDLean.PNT.psi_eq_theta_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psi_eq_theta_add

/-- info: 'TDLean.PNT.card_ppSet_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.card_ppSet_le

/-- info: 'TDLean.PNT.psiErr_le_card_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psiErr_le_card_mul

/-- info: 'TDLean.PNT.log_le_four_mul_sqrt_sqrt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.log_le_four_mul_sqrt_sqrt

/-- info: 'TDLean.PNT.psiErr_mul_log2_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psiErr_mul_log2_le

/-- info: 'TDLean.PNT.psi_le_const_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psi_le_const_mul

/-! ### C10 part 2: Abel summation -/

/-- info: 'TDLean.PNT.sum_LamC_eq_psi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.sum_LamC_eq_psi

/-- info: 'TDLean.PNT.deriv_kernel_eqOn' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.deriv_kernel_eqOn

/-- info: 'TDLean.PNT.abel_finite' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.abel_finite

/-- info: 'TDLean.PNT.psi_mono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psi_mono

/-- info: 'TDLean.PNT.Ccheb_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.Ccheb_nonneg

/-- info: 'TDLean.PNT.integrableOn_mellin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integrableOn_mellin

/-- info: 'TDLean.PNT.tendsto_boundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_boundary

/-- info: 'TDLean.PNT.summable_LamC_nat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.summable_LamC_nat

/-- info: 'TDLean.PNT.tendsto_partial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_partial

/-- info: 'TDLean.PNT.LS_LamC_eq_mellin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.LS_LamC_eq_mellin

/-- info: 'TDLean.PNT.exp_image_Ioi_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.exp_image_Ioi_zero

/-- info: 'TDLean.PNT.ofReal_exp_cpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.ofReal_exp_cpow

/-- info: 'TDLean.PNT.mellin_change_of_variable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.mellin_change_of_variable

/-- info: 'TDLean.PNT.norm_fNewmanC_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.norm_fNewmanC_le

/-- info: 'TDLean.PNT.intervalIntegrable_fNewmanC' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.intervalIntegrable_fNewmanC

/-- info: 'TDLean.PNT.psi_exp_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psi_exp_eq

/-- info: 'TDLean.PNT.integral_cexp_neg_interval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integral_cexp_neg_interval

/-- info: 'TDLean.PNT.integrableOn_cexp_neg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integrableOn_cexp_neg

/-- info: 'TDLean.PNT.integral_cexp_neg_Ioi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integral_cexp_neg_Ioi

/-- info: 'TDLean.PNT.integrableOn_fNewman_exp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integrableOn_fNewman_exp

/-- info: 'TDLean.PNT.mellin_eq_laplace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.mellin_eq_laplace

/-- info: 'TDLean.PNT.gNewman_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.gNewman_eq

/-- info: 'TDLean.PNT.isOpen_gRegion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.isOpen_gRegion

/-- info: 'TDLean.PNT.differentiableOn_gNewman' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.differentiableOn_gNewman

/-- info: 'TDLean.PNT.rightHalfplane_subset_gRegion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.rightHalfplane_subset_gRegion

/-- info: 'TDLean.PNT.contourSet_subset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.contourSet_subset

/-- info: 'TDLean.PNT.hregion_gNewman' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.hregion_gNewman

/-- info: 'TDLean.PNT.tendsto_integral_fNewman' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_integral_fNewman

/-- info: 'TDLean.PNT.gT_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.gT_zero

/-- info: 'TDLean.PNT.tendsto_integral_fNewman'' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_integral_fNewman'

/-! ### The identity theorem in real-ray form (LEDGER finding #1's actual tool) -/

/-- info: 'TDLean.Zeta.eqOn_of_eqOn_seq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.eqOn_of_eqOn_seq

/-- info: 'TDLean.Zeta.tendsto_realApproach' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.tendsto_realApproach

/-- info: 'TDLean.Zeta.eqOn_of_eqOn_realRay' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.eqOn_of_eqOn_realRay

/-- info: 'TDLean.Zeta.eqOn_realRay_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.eqOn_realRay_nonvacuous

/-! ### Complex ell-2 with an adjoint (the Rocq Ell2 line is over R) -/

/-- info: 'TDLean.Operator.summable_ip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.summable_ip

/-- info: 'TDLean.Operator.ell2_diag' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ell2_diag

/-- info: 'TDLean.Operator.ip_diag_adjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ip_diag_adjoint

/-- info: 'TDLean.Operator.ip_diag_selfadjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ip_diag_selfadjoint

/-- info: 'TDLean.Operator.ip_delta_diag' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ip_delta_diag

/-- info: 'TDLean.Operator.eigenvalue_real_of_selfadjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.eigenvalue_real_of_selfadjoint

/-- info: 'TDLean.Operator.trace_zetaKernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.trace_zetaKernel

/-- info: 'TDLean.Operator.isHermitian_zetaKernel_of_real' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.isHermitian_zetaKernel_of_real

/-! ### The number operator and the partition function -/

/-- info: 'TDLean.Operator.numberOp_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.numberOp_mul

/-- info: 'TDLean.Operator.numberOp_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.numberOp_pow

/-- info: 'TDLean.Operator.numberOp_eq_sum_vonMangoldt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.numberOp_eq_sum_vonMangoldt

/-- info: 'TDLean.Operator.isHermitian_numberOp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.isHermitian_numberOp

/-- info: 'TDLean.Operator.gibbs_eq_zetaKernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.gibbs_eq_zetaKernel

/-- info: 'TDLean.Operator.partitionFunction_eq_zeta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.partitionFunction_eq_zeta

/-- info: 'TDLean.Operator.partitionFunction_diverges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.partitionFunction_diverges

/-! ### The prime-shift isometries: S*S = 1 but SS* /= 1 -/

/-- info: 'TDLean.Operator.coshift_shift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.coshift_shift

/-- info: 'TDLean.Operator.ell2_shift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ell2_shift

/-- info: 'TDLean.Operator.ip_shift_adjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ip_shift_adjoint

/-- info: 'TDLean.Operator.shift_coshift_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.shift_coshift_apply

/-- info: 'TDLean.Operator.shift_coshift_ne_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.shift_coshift_ne_id

/-- info: 'TDLean.Operator.coshift_coshift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.coshift_coshift

/-- info: 'TDLean.Operator.numberOp_covariance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.numberOp_covariance

/-- info: 'TDLean.Operator.numberOp_commutator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.numberOp_commutator

/-! ### The Bost-Connes relations as an algebra presentation -/

/-- info: 'TDLean.Operator.shift_shift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.shift_shift

/-- info: 'TDLean.Operator.shift_coshift_comm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.shift_coshift_comm

/-- info: 'TDLean.Operator.not_comm_of_not_coprime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.not_comm_of_not_coprime

/-- info: 'TDLean.Operator.ip_coshift_adjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ip_coshift_adjoint

/-- info: 'TDLean.Operator.bc_isometry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.bc_isometry

/-- info: 'TDLean.Operator.bc_semigroup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.bc_semigroup

/-- info: 'TDLean.Operator.bc_coprime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.bc_coprime

/-- info: 'TDLean.Operator.bc_not_unitary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.bc_not_unitary

/-- info: 'TDLean.Operator.Sop_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.Sop_mem

/-- info: 'TDLean.Operator.Sadj_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.Sadj_mem

/-! ### Q/Z, its group algebra, and the BC coupling relation -/

/-- info: 'TDLean.Operator.exists_nsmul_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.exists_nsmul_eq

/-- info: 'TDLean.Operator.torsionEmb_torsion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.torsionEmb_torsion

/-- info: 'TDLean.Operator.torsionEmb_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.torsionEmb_injective

/-- info: 'TDLean.Operator.torsionEmb_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.torsionEmb_surjective

/-- info: 'TDLean.Operator.nsmul_eq_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.nsmul_eq_iff

/-- info: 'TDLean.Operator.egen_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.egen_mul

/-- info: 'TDLean.Operator.egen_mul_neg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.egen_mul_neg

/-- info: 'TDLean.Operator.couple_indexes_fibre' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.couple_indexes_fibre

/-! ### The Bost-Connes representation on ell-2 -/

/-- info: 'TDLean.Operator.chi_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.chi_add

/-- info: 'TDLean.Operator.chi_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.chi_zero

/-- info: 'TDLean.Operator.norm_chi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.norm_chi

/-- info: 'TDLean.Operator.chi_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.chi_conj

/-- info: 'TDLean.Operator.Eop_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.Eop_mul

/-- info: 'TDLean.Operator.Eop_mul_neg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.Eop_mul_neg

/-- info: 'TDLean.Operator.ip_Eop_adjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.ip_Eop_adjoint

/-- info: 'TDLean.Operator.conj_Eop_apply_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.conj_Eop_apply_mul

/-- info: 'TDLean.Operator.conj_Eop_apply_of_not_dvd' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.conj_Eop_apply_of_not_dvd

/-! ### Root-of-unity sum and the BC coupling relation -/

/-- info: 'TDLean.Operator.isPrimitiveRoot_zetaRoot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.isPrimitiveRoot_zetaRoot

/-- info: 'TDLean.Operator.chi_torsionEmb_nsmul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.chi_torsionEmb_nsmul

/-- info: 'TDLean.Operator.zetaRoot_pow_eq_one_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.zetaRoot_pow_eq_one_iff

/-- info: 'TDLean.Operator.sum_chi_torsion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.sum_chi_torsion

/-- info: 'TDLean.Operator.bc_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Operator.bc_coupling

/-! ### C10 part 10: the squeeze machinery -/

/-- info: 'TDLean.PNT.cauchy_tail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.cauchy_tail

/-- info: 'TDLean.PNT.overshoot_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.overshoot_pos

/-- info: 'TDLean.PNT.undershoot_neg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.undershoot_neg

/-- info: 'TDLean.PNT.integral_model' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integral_model

/-- info: 'TDLean.PNT.fNewman_ge_model' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.fNewman_ge_model

/-- info: 'TDLean.PNT.integral_ge_overshoot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integral_ge_overshoot

/-- info: 'TDLean.PNT.integral_le_undershoot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.integral_le_undershoot

/-- info: 'TDLean.PNT.no_overshoot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.no_overshoot

/-- info: 'TDLean.PNT.no_undershoot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.no_undershoot

/-- info: 'TDLean.PNT.tendsto_psi_exp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_psi_exp

/-- info: 'TDLean.PNT.tendsto_psi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_psi

/-! ### C10 part 11: psi ~ x implies theta ~ x -/

/-- info: 'TDLean.PNT.psiErr_mul_log2_le'' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psiErr_mul_log2_le'

/-- info: 'TDLean.PNT.psiErr_le_rpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psiErr_le_rpow

/-- info: 'TDLean.PNT.psiErr_div_tendsto_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.psiErr_div_tendsto_zero

/-- info: 'TDLean.PNT.tendsto_theta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_theta

/-! ### C10 part 12: the prime-counting function -/

/-- info: 'TDLean.PNT.theta_le_piCount_mul_log' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.theta_le_piCount_mul_log

/-- info: 'TDLean.PNT.card_small_primes_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.card_small_primes_le

/-- info: 'TDLean.PNT.piCount_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.piCount_le

/-! ### C10 part 13: the Prime Number Theorem -/

/-- info: 'TDLean.PNT.tendsto_rpow_mul_log_div' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_rpow_mul_log_div

/-- info: 'TDLean.PNT.tendsto_piCount' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.PNT.tendsto_piCount

/-! ### Cluster A1: Gaussian decay (rebuilt; the banned file has these) -/

/-- info: 'TDLean.FE.gaussian_isLittleO_atTop' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.gaussian_isLittleO_atTop

/-- info: 'TDLean.FE.gaussian_isLittleO_cocompact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.gaussian_isLittleO_cocompact

/-- info: 'TDLean.FE.tsum_gaussian_transform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.tsum_gaussian_transform

/-! ### Cluster A3: the single-term Mellin integral -/

/-- info: 'TDLean.FE.cpow_pos_eq_exp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.cpow_pos_eq_exp

/-- info: 'TDLean.FE.scale_factor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.scale_factor

/-- info: 'TDLean.FE.mellin_gaussian_term' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.mellin_gaussian_term

/-- info: 'TDLean.FE.integrableOn_gaussian_term' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_gaussian_term

/-- info: 'TDLean.FE.norm_gaussian_term' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_gaussian_term

/-! ### Conjugation symmetry and the critical line -/

/-- info: 'TDLean.Zeta.conj_cpow_ofReal_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.conj_cpow_ofReal_pos

/-- info: 'TDLean.Zeta.conj_intervalIntegral' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.conj_intervalIntegral

/-- info: 'TDLean.Zeta.zetaDiff_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaDiff_conj

/-- info: 'TDLean.Zeta.zetaDiffSum_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaDiffSum_conj

/-- info: 'TDLean.Zeta.zetaCont_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_conj

/-- info: 'TDLean.Zeta.zetaCont_eq_zero_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_eq_zero_conj

/-- info: 'TDLean.Zeta.refl_involutive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.refl_involutive

/-- info: 'TDLean.Zeta.refl_fixed_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.refl_fixed_iff

/-- info: 'TDLean.Zeta.fixedPoints_refl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.fixedPoints_refl

/-- info: 'TDLean.Zeta.RH_iff_zeros_refl_fixed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.RH_iff_zeros_refl_fixed

/-- info: 'TDLean.Zeta.zeros_conj_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zeros_conj_invariant

/-- info: 'TDLean.Zeta.zeros_refl_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zeros_refl_invariant

/-- info: 'TDLean.Zeta.criticalLine_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.criticalLine_nonvacuous

/-! ### The critical strip (right edge) and the interchange bound -/

/-- info: 'TDLean.Zeta.zetaCont_zero_re_lt_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_zero_re_lt_one

/-- info: 'TDLean.Zeta.zetaCont_zeros_in_strip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.zetaCont_zeros_in_strip

/-- info: 'TDLean.Zeta.strip_conj_closed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.Zeta.strip_conj_closed

/-- info: 'TDLean.FE.integrableOn_real_term' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_real_term

/-- info: 'TDLean.FE.integral_norm_term' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integral_norm_term

/-- info: 'TDLean.FE.lintegral_norm_summable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.lintegral_norm_summable

/-- info: 'TDLean.FE.mellin_psiTheta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.mellin_psiTheta

/-! ### Cluster A6: Gaussian summability and the theta-to-psi bridge -/

/-- info: 'TDLean.FE.norm_gaussian' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_gaussian

/-- info: 'TDLean.FE.summable_gaussian_nat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.summable_gaussian_nat

/-- info: 'TDLean.FE.summable_gaussian_int' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.summable_gaussian_int

/-- info: 'TDLean.FE.summable_psiNat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.summable_psiNat

/-- info: 'TDLean.FE.tsum_gaussian_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.tsum_gaussian_eq

/-! ### Cluster A7: psi's transformation law -/

/-- info: 'TDLean.FE.cpow_half_eq_sqrt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.cpow_half_eq_sqrt

/-- info: 'TDLean.FE.psiNat_transform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.psiNat_transform

/-- info: 'TDLean.FE.psiTheta_eq_psiNat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.psiTheta_eq_psiNat

/-- info: 'TDLean.FE.psiTheta_transform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.psiTheta_transform

/-! ### Cluster A8: the elementary pole terms -/

/-- info: 'TDLean.FE.sqrt_eq_cpow_half' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.sqrt_eq_cpow_half

/-- info: 'TDLean.FE.pole_integrand_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.pole_integrand_eq

/-- info: 'TDLean.FE.integral_pole_terms' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integral_pole_terms

/-! ### Cluster A9: the change of variable `t ↦ 1/u` -/

/-- info: 'TDLean.FE.inv_image_Ioi_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.inv_image_Ioi_one

/-- info: 'TDLean.FE.inv_cpow_ofReal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.inv_cpow_ofReal

/-- info: 'TDLean.FE.ofReal_sq_inv_eq_cpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.ofReal_sq_inv_eq_cpow

/-- info: 'TDLean.FE.integral_Ioo_eq_integral_Ioi_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integral_Ioo_eq_integral_Ioi_inv

/-! ### Cluster A10-A12: decay, integrability, and the functional equation -/

/-- info: 'TDLean.FE.norm_psiNat_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_psiNat_le

/-- info: 'TDLean.FE.norm_psiTheta_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_psiTheta_le

/-- info: 'TDLean.FE.aestronglyMeasurable_psiTheta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.aestronglyMeasurable_psiTheta

/-- info: 'TDLean.FE.integrableOn_rpow_mul_exp_neg_pi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_rpow_mul_exp_neg_pi

/-- info: 'TDLean.FE.integrableOn_cpow_mul_psiTheta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_cpow_mul_psiTheta

/-- info: 'TDLean.FE.folded_integrand_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.folded_integrand_eq

/-- info: 'TDLean.FE.integrableOn_folded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_folded

/-- info: 'TDLean.FE.integrableOn_mellin_Ioo' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_mellin_Ioo

/-- info: 'TDLean.FE.completedZeta_symm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_symm

/-- info: 'TDLean.FE.mellin_eq_completedZeta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.mellin_eq_completedZeta

/-- info: 'TDLean.FE.completedZeta_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_eq

/-! ### Cluster A13: the critical strip, trivial zeros, and the Klein four-group -/

/-- info: 'TDLean.FE.completedZeta_ne_zero_of_one_lt_re' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_ne_zero_of_one_lt_re

/-- info: 'TDLean.FE.completedZeta_ne_zero_of_re_lt_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_ne_zero_of_re_lt_zero

/-- info: 'TDLean.FE.completedZeta_zeros_in_strip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_zeros_in_strip

/-- info: 'TDLean.FE.completedZeta_ne_zero_nonvacuous' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_ne_zero_nonvacuous

/-- info: 'TDLean.FE.zetaFE_eq_zetaSeries' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaFE_eq_zetaSeries

/-- info: 'TDLean.FE.zetaFE_trivial_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaFE_trivial_zero

/-- info: 'TDLean.FE.completedZeta_ne_zero_at_trivial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_ne_zero_at_trivial

/-- info: 'TDLean.FE.conj_psiTheta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.conj_psiTheta

/-- info: 'TDLean.FE.completedZeta_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_conj

/-- info: 'TDLean.FE.completedZeta_zero_quadruple' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_zero_quadruple

/-- info: 'TDLean.FE.completedZeta_zeros_refl_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_zeros_refl_invariant

/-! ### Cluster A14: holomorphy of the tail transform and of Lambda -/

/-- info: 'TDLean.FE.integrableOn_log_mul_rpow_mul_exp_neg_pi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_log_mul_rpow_mul_exp_neg_pi

/-- info: 'TDLean.FE.integrableOn_log_mul_cpow_mul_psiTheta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integrableOn_log_mul_cpow_mul_psiTheta

/-- info: 'TDLean.FE.hasDerivAt_mellinTail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.hasDerivAt_mellinTail

/-- info: 'TDLean.FE.differentiable_mellinTail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.differentiable_mellinTail

/-- info: 'TDLean.FE.completedZeta_eq_mellinTail' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_eq_mellinTail

/-- info: 'TDLean.FE.differentiableAt_completedZeta' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.differentiableAt_completedZeta

/-! ### Cluster A15: the identity transferred into the strip -/

/-- info: 'TDLean.FE.poleFreeL_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.poleFreeL_eq

/-- info: 'TDLean.FE.poleFreeR_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.poleFreeR_eq

/-- info: 'TDLean.FE.differentiableOn_poleFreeL' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.differentiableOn_poleFreeL

/-- info: 'TDLean.FE.differentiableOn_poleFreeR' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.differentiableOn_poleFreeR

/-- info: 'TDLean.FE.eqOn_poleFree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.eqOn_poleFree

/-- info: 'TDLean.FE.completedZeta_eq_zetaCont' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_eq_zetaCont

/-- info: 'TDLean.FE.completedZeta_eq_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_eq_zero_iff

/-- info: 'TDLean.FE.zetaCont_zero_refl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaCont_zero_refl

/-- info: 'TDLean.FE.zetaCont_zero_quadruple' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaCont_zero_quadruple

/-! ### Cluster A16: the full continuation and the genuine trivial zeros -/

/-- info: 'TDLean.FE.differentiable_inv_Gamma_half' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.differentiable_inv_Gamma_half

/-- info: 'TDLean.FE.differentiableAt_zetaFE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.differentiableAt_zetaFE

/-- info: 'TDLean.FE.zetaFE_eq_zetaCont' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaFE_eq_zetaCont

/-- info: 'TDLean.FE.zetaFE_trivial_zero_genuine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaFE_trivial_zero_genuine

/-- info: 'TDLean.FE.zetaFE_eq_zero_iff_of_re_lt_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaFE_eq_zero_iff_of_re_lt_zero

/-! ### Cluster A17: the classical functional equation -/

/-- info: 'TDLean.FE.gamma_half_sub_eq_zero_of_cos_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.gamma_half_sub_eq_zero_of_cos_eq_zero

/-- info: 'TDLean.FE.inv_Gamma_half_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.inv_Gamma_half_sub

/-- info: 'TDLean.FE.gamma_ratio' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.gamma_ratio

/-- info: 'TDLean.FE.pi_power_collapse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.pi_power_collapse

/-- info: 'TDLean.FE.two_pi_cpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.two_pi_cpow

/-- info: 'TDLean.FE.zetaFE_functional_equation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaFE_functional_equation

/-- info: 'TDLean.FE.zetaFE_trivial_zero_via_cos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.zetaFE_trivial_zero_via_cos

/-! ### Cluster A18: Lambda real on the critical line, and Lambda(1/2) < 0 -/

/-- info: 'TDLean.FE.completedZeta_refl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_refl

/-- info: 'TDLean.FE.completedZeta_conj_eq_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_conj_eq_self

/-- info: 'TDLean.FE.completedZeta_im_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_im_eq_zero

/-- info: 'TDLean.FE.psiBound_le_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.psiBound_le_two

/-- info: 'TDLean.FE.norm_integral_half_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_integral_half_le

/-- info: 'TDLean.FE.completedZeta_half_re_lt_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.completedZeta_half_re_lt_zero

/-! ### Cluster A19: Riemann's xi, entire -/

/-- info: 'TDLean.FE.differentiable_xi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.differentiable_xi

/-- info: 'TDLean.FE.xi_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_eq

/-- info: 'TDLean.FE.xi_symm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_symm

/-- info: 'TDLean.FE.xi_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_zero

/-- info: 'TDLean.FE.xi_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_one

/-- info: 'TDLean.FE.xi_eq_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_eq_zero_iff

/-- info: 'TDLean.FE.xi_zeros_in_strip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_zeros_in_strip

/-- info: 'TDLean.FE.xi_conj_eq_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_conj_eq_self

/-- info: 'TDLean.FE.xi_im_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_im_eq_zero

/-- info: 'TDLean.FE.xi_half_re_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_half_re_pos

/-! ### Cluster A20: growth bounds (the Hadamard-route input) -/

/-- info: 'TDLean.FE.integral_rpow_mul_exp_neg_pi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.integral_rpow_mul_exp_neg_pi

/-- info: 'TDLean.FE.norm_mellinTail_le_gamma' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_mellinTail_le_gamma

/-- info: 'TDLean.FE.norm_mellinTail_le_of_nonpos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_mellinTail_le_of_nonpos

/-- info: 'TDLean.FE.norm_xi_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.norm_xi_le

/-! ### Cluster A21: the critical line as one real function -/

/-- info: 'TDLean.FE.mellinTail_conj' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.mellinTail_conj

/-- info: 'TDLean.FE.xi_critical_formula' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_critical_formula

/-- info: 'TDLean.FE.xi_critical_formula_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_critical_formula_zero

/-- info: 'TDLean.FE.Zline_zero_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.Zline_zero_pos

/-- info: 'TDLean.FE.xi_eq_zero_of_Zline_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TDLean.FE.xi_eq_zero_of_Zline_eq_zero
