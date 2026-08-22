(* ================================================================= *)
(*  ZeroFreeRegion.v  --  the assembly.                                *)
(*                                                                    *)
(*  region_from_inputs collects the whole zero-free-region argument    *)
(*  into one algebraic step, taking as inputs exactly what the three   *)
(*  analytic files supply at the single point a = 1 + 81/(256 K):      *)
(*                                                                    *)
(*    from CHorizMVT.horiz_mvt (with zeta(rho) = 0):                   *)
(*        |zeta(a + i.g)| <= 2 (a - beta) M                            *)
(*    from ZetaLowerBound.zeta_lower_log:                              *)
(*        (a - 1)^3 <= A |zeta(a + i.g)|^4                             *)
(*                                                                    *)
(*  and returning  beta <= 1 - 27/(256 K),  K = 16 A M^4.              *)
(*                                                                    *)
(*  Everything analytic has already happened by the time this lemma is *)
(*  reached; what is left is raising the first bound to the fourth     *)
(*  power, substituting, and invoking ZeroFreeOpt.quartic_opt.  Keeping *)
(*  it separate from the wiring matters: this is the step where a      *)
(*  mis-stated exponent would produce a theorem that type-checks and   *)
(*  says nothing, so it is worth being able to read it on its own.     *)
(*  Axiom-clean.                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic ZetaFn ZetaDeriv
        CHorizMVT ZetaLogBound ZetaLowerBound CriticalDepth ZeroFreeOpt.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the algebraic core                                                 *)
(* ----------------------------------------------------------------- *)
Theorem region_from_inputs : forall beta g K M A V,
  0 <= M -> 0 <= A -> 0 < K -> K = 16 * A * M ^ 4 ->
  beta <= 1 ->
  V = Cmod (zF (mkC (1 + 81 / (256 * K)) g)) ->
  V <= 2 * (1 + 81 / (256 * K) - beta) * M ->
  (81 / (256 * K)) ^ 3 <= A * V ^ 4 ->
  beta <= 1 - 27 / (256 * K).
Proof.
  intros beta g K M A V HM HA HK HKdef Hb HV HMVT Hlow.
  set (dl := 81 / (256 * K)) in *.
  set (u := 1 - beta).
  assert (Hu0 : 0 <= u) by (unfold u; lra).
  assert (Hdl0 : 0 < dl) by (unfold dl; apply Rdiv_lt_0_compat; lra).
  assert (Hsum : 1 + dl - beta = u + dl) by (unfold u; ring).
  assert (HV0 : 0 <= V) by (rewrite HV; apply Cmod_nonneg).
  (* raise the mean value bound to the fourth power *)
  assert (Hpos : 0 <= 2 * (u + dl) * M) by nra.
  assert (HV4 : V ^ 4 <= (2 * (u + dl) * M) ^ 4).
  { apply pow_incr. split; [ exact HV0 | rewrite <- Hsum; exact HMVT ]. }
  assert (Hexp : (2 * (u + dl) * M) ^ 4 = 16 * M ^ 4 * (u + dl) ^ 4) by ring.
  rewrite Hexp in HV4.
  (* feed it through the 3-4-1 lower bound *)
  assert (HAV : A * V ^ 4 <= A * (16 * M ^ 4 * (u + dl) ^ 4))
    by (apply Rmult_le_compat_l; [ exact HA | exact HV4 ]).
  assert (HKeq : A * (16 * M ^ 4 * (u + dl) ^ 4) = K * (u + dl) ^ 4)
    by (rewrite HKdef; ring).
  rewrite HKeq in HAV.
  assert (Hquart : dl ^ 3 <= K * (u + dl) ^ 4) by lra.
  (* and optimise *)
  pose proof (quartic_opt u K HK Hu0 Hquart) as Hopt.
  unfold u in Hopt. lra.
Qed.

Print Assumptions region_from_inputs.

(* ----------------------------------------------------------------- *)
(*  the wiring: from a zero of zeta to the region                      *)
(* ----------------------------------------------------------------- *)
(*  The derivative facts are taken as hypotheses on the SEGMENT rather *)
(*  than re-derived here, because that is exactly the interface the    *)
(*  two analytic files present: ZetaDeriv.zF_deriv supplies the first, *)
(*  ZetaDerivBoundExt.zeta_deriv_log_bound_ext the second, and both    *)
(*  need side conditions (inDom, and 1 - d <= Re s) that belong with   *)
(*  the caller's case split on how close beta is to 1.                 *)
(* ----------------------------------------------------------------- *)
Theorem region_of_zero : forall beta g M K,
  0 < M -> 1 <= Rabs g -> 0 < beta -> beta <= 1 ->
  K = 16 * (343 * (ln (2 * Rabs g) + 10)) * M ^ 4 ->
  zF (mkC beta g) = C0 ->
  81 / (256 * K) <= 1 ->
  (forall x, beta <= x <= 1 + 81 / (256 * K) ->
     is_Cderiv zF (mkC x g) (zDF (mkC x g))) ->
  (forall x, beta <= x <= 1 + 81 / (256 * K) -> Cmod (zDF (mkC x g)) <= M) ->
  beta <= 1 - 27 / (256 * K).
Proof.
  intros beta g M K HM Hg Hb0 Hb1 HKdef Hzero Hdl1 Hder Hbd.
  assert (HlnA : 0 <= ln (2 * Rabs g)) by (apply ln_nonneg; lra).
  assert (HA : 0 < 343 * (ln (2 * Rabs g) + 10)) by lra.
  assert (HM4 : 0 < M ^ 4) by (apply pow_lt; exact HM).
  assert (HK : 0 < K) by (rewrite HKdef; nra).
  assert (Hdl0 : 0 < 81 / (256 * K)) by (apply Rdiv_lt_0_compat; lra).
  assert (Ha1 : 1 < 1 + 81 / (256 * K)) by lra.
  assert (Ha2 : 1 + 81 / (256 * K) <= 2) by lra.
  assert (Hba : beta <= 1 + 81 / (256 * K)) by lra.
  (* the mean value step, with zeta(rho) = 0 *)
  pose proof (horiz_mvt zF zDF beta (1 + 81 / (256 * K)) g M
                Hba ltac:(lra) Hder Hbd) as HMV.
  rewrite Hzero in HMV.
  assert (Esub : Cmod (Cminus (zF (mkC (1 + 81 / (256 * K)) g)) C0)
               = Cmod (zF (mkC (1 + 81 / (256 * K)) g)))
    by (unfold Cmod, Cnorm2, Cminus, C0; cbn [Re Im]; f_equal; ring).
  rewrite Esub in HMV.
  (* the 3-4-1 lower bound at a = 1 + delta *)
  pose proof (zeta_lower_log (1 + 81 / (256 * K)) g Ha1 Ha2 Hg) as HLB.
  assert (Ea : 1 + 81 / (256 * K) - 1 = 81 / (256 * K)) by ring.
  rewrite Ea in HLB.
  (* and the algebraic core *)
  apply (region_from_inputs beta g K M (343 * (ln (2 * Rabs g) + 10))
           (Cmod (zF (mkC (1 + 81 / (256 * K)) g))));
    try assumption; try reflexivity; try lra.
Qed.

Print Assumptions region_of_zero.


(* ----------------------------------------------------------------- *)
(*  the derivative hypothesis is free -- zF is differentiable on the   *)
(*  whole segment, since Re >= beta > 0 and z <> 1 because Im = g <> 0 *)
(* ----------------------------------------------------------------- *)
Lemma deriv_on_segment : forall beta g x, 0 < beta -> beta <= x -> 1 <= Rabs g ->
  is_Cderiv zF (mkC x g) (zDF (mkC x g)).
Proof.
  intros beta g x Hb Hx Hg. apply zF_deriv. unfold inDom. split.
  - cbn [Re]. lra.
  - intro Hc. apply (f_equal Im) in Hc.
    unfold Cminus, C1, C0 in Hc; cbn [Re Im] in Hc.
    assert (Hg0 : g = 0) by lra.
    rewrite Hg0, Rabs_R0 in Hg. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE REGION, AND ITS DEPTH                                          *)
(* ----------------------------------------------------------------- *)
Theorem region_of_zero' : forall beta g M K,
  0 < M -> 1 <= Rabs g -> 0 < beta -> beta <= 1 ->
  K = 16 * (343 * (ln (2 * Rabs g) + 10)) * M ^ 4 ->
  zF (mkC beta g) = C0 ->
  81 / (256 * K) <= 1 ->
  (forall x, beta <= x <= 1 + 81 / (256 * K) -> Cmod (zDF (mkC x g)) <= M) ->
  beta <= 1 - 27 / (256 * K).
Proof.
  intros beta g M K HM Hg Hb0 Hb1 HKdef Hzero Hdl1 Hbd.
  apply (region_of_zero beta g M K); try assumption.
  intros x Hx. apply (deriv_on_segment beta g x); [ exact Hb0 | lra | exact Hg ].
Qed.

Corollary depth_of_zero : forall beta g M K,
  0 < M -> 1 <= Rabs g -> 0 < beta -> beta <= 1 ->
  K = 16 * (343 * (ln (2 * Rabs g) + 10)) * M ^ 4 ->
  zF (mkC beta g) = C0 ->
  81 / (256 * K) <= 1 ->
  (forall x, beta <= x <= 1 + 81 / (256 * K) -> Cmod (zDF (mkC x g)) <= M) ->
  depth (mkC beta g) <= ln (256 * K / 27).
Proof.
  intros beta g M K HM Hg Hb0 Hb1 HKdef Hzero Hdl1 Hbd.
  assert (HlnA : 0 <= ln (2 * Rabs g)) by (apply ln_nonneg; lra).
  assert (HM4 : 0 < M ^ 4) by (apply pow_lt; exact HM).
  assert (HK : 0 < K) by (rewrite HKdef; nra).
  assert (H81 : 81 <= 256 * K).
  { assert (E : 81 / (256 * K) * (256 * K) = 81) by (field; lra). nra. }
  apply (depth_of_quartic (mkC beta g) K HK ltac:(lra));
    [ cbn [Re]; lra | ].
  cbn [Re]. apply (region_of_zero' beta g M K); assumption.
Qed.

Print Assumptions region_of_zero'.
Print Assumptions depth_of_zero.
