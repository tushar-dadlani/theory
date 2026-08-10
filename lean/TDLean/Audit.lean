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
import TDLean.Newman.Tauberian

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
