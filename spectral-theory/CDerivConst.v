(* ================================================================= *)
(*  CDerivConst.v  —  Hadamard keystone, brick B core:                  *)
(*  a complex derivative identically 0 on a convex set => constant.     *)
(*                                                                    *)
(*    Cderiv0_const : Convex U -> (forall z in U, is_Cderiv H z C0) ->  *)
(*                    forall a b in U, H a = H b.                       *)
(*                                                                    *)
(*  This is the one genuinely-missing lemma for the HOLOMORPHIC COMPLEX *)
(*  LOGARITHM (brick B): with G a primitive of F'/F (from brick A,      *)
(*  CPrimitiveDisk.primitive_on_disk), the function F.e^{-G} has        *)
(*  derivative 0, so by THIS lemma it is constant = F(0), giving        *)
(*  F(z) = F(0).e^{G(z)} -- the log/exp relation that unblocks the      *)
(*  zero-free mean value property (brick 3) and Hadamard uniqueness.    *)
(*                                                                    *)
(*  Proof: on the segment c(t)=seg a b t (inside U by convexity), the   *)
(*  real functions t |-> Re(H(c t)) and t |-> Im(H(c t)) have real      *)
(*  derivative 0 (from is_Cderiv H (c t) C0, since |Re w|,|Im w|<=|w|), *)
(*  hence are constant on [0,1] (MVT), so H a = H(c 0) = H(c 1) = H b.   *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CSeries CPrimConv CPathIntegral Holomorphic.
Open Scope R_scope.

Lemma ReCm : forall a b, Re (Cminus a b) = Re a - Re b.
Proof. intros [ra ia] [rb ib]; simpl; ring. Qed.

Lemma ImCm : forall a b, Im (Cminus a b) = Im a - Im b.
Proof. intros [ra ia] [rb ib]; simpl; ring. Qed.

(* the real-parameter derivative of a projection of H along a segment is 0 *)
Lemma curve_comp_deriv0 :
  forall (proj : C -> R),
  (forall w, Rabs (proj w) <= Cmod w) ->
  (forall x y, proj (Cminus x y) = proj x - proj y) ->
  forall H a b t, is_Cderiv H (seg a b t) C0 ->
  derivable_pt_lim (fun s => proj (H (seg a b s))) t 0.
Proof.
  intros proj Hbd Hmin H a b t Hd eps Heps.
  set (K := Cmod (Cminus b a) + 1).
  assert (HK : 0 < K) by (unfold K; pose proof (Cmod_nonneg (Cminus b a)); lra).
  destruct (Hd (eps / K) (Rdiv_lt_0_compat eps K Heps HK)) as [del' [Hdel' Hb']].
  assert (Hdelpos : 0 < del' / K) by (apply Rdiv_lt_0_compat; assumption).
  exists (mkposreal (del' / K) Hdelpos).
  intros h Hh0 Hh. simpl in Hh.
  set (k := Cmul (RtoC h) (Cminus b a)).
  assert (Hseg : seg a b (t + h) = Cadd (seg a b t) k).
  { unfold seg, k. rewrite RtoC_add. ring. }
  assert (Hkmod : Cmod k = Rabs h * Cmod (Cminus b a))
    by (unfold k; rewrite Cmod_mul, Cmod_RtoC; reflexivity).
  assert (Hklt : Cmod k < del').
  { rewrite Hkmod. apply Rle_lt_trans with (Rabs h * K).
    - apply Rmult_le_compat_l; [ apply Rabs_pos | unfold K; lra ].
    - apply Rlt_le_trans with (del' / K * K).
      + apply Rmult_lt_compat_r; [ exact HK | exact Hh ].
      + right; field; lra. }
  specialize (Hb' k Hklt).
  replace (Cmul C0 k) with C0 in Hb' by ring.
  replace (Cminus (Cminus (H (Cadd (seg a b t) k)) (H (seg a b t))) C0)
     with (Cminus (H (Cadd (seg a b t) k)) (H (seg a b t))) in Hb' by ring.
  rewrite <- Hseg in Hb'.
  assert (HD : Rabs (proj (H (seg a b (t + h))) - proj (H (seg a b t))) <= eps / K * Cmod k).
  { rewrite <- Hmin. eapply Rle_trans; [ apply Hbd | exact Hb' ]. }
  rewrite Rminus_0_r. unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  apply Rle_lt_trans with (eps / K * Cmod (Cminus b a)).
  - apply Rmult_le_reg_r with (Rabs h); [ apply Rabs_pos_lt; exact Hh0 | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0; exact Hh0).
    eapply Rle_trans; [ exact HD | ]. rewrite Hkmod. right; ring.
  - assert (Hm : 0 <= Cmod (Cminus b a)) by apply Cmod_nonneg.
    apply Rlt_le_trans with (eps / K * (Cmod (Cminus b a) + 1)).
    + apply Rmult_lt_compat_l; [ apply Rdiv_lt_0_compat; [ exact Heps | exact HK ] | lra ].
    + unfold K. right; field; lra.
Qed.

(* THE lemma: complex derivative 0 on a convex set => constant *)
Theorem Cderiv0_const : forall (U : C -> Prop), Convex U ->
  forall H, (forall z, U z -> is_Cderiv H z C0) ->
  forall a b, U a -> U b -> H a = H b.
Proof.
  intros U HU H Hd a b Ha Hb.
  assert (Hcurve : forall t, 0 <= t <= 1 -> U (seg a b t)) by (intros t Ht; apply HU; assumption).
  assert (HdR : forall c, 0 <= c <= 1 -> derivable_pt_lim (fun t => Re (H (seg a b t))) c 0)
    by (intros c Hc; apply (curve_comp_deriv0 Re Cmod_Re_le ReCm H a b c); apply Hd, Hcurve, Hc).
  assert (HdI : forall c, 0 <= c <= 1 -> derivable_pt_lim (fun t => Im (H (seg a b t))) c 0)
    by (intros c Hc; apply (curve_comp_deriv0 Im Cmod_Im_le ImCm H a b c); apply Hd, Hcurve, Hc).
  destruct (MVT_cor2 (fun t => Re (H (seg a b t))) (fun _ => 0) 0 1 Rlt_0_1 HdR) as [cR [HR _]].
  destruct (MVT_cor2 (fun t => Im (H (seg a b t))) (fun _ => 0) 0 1 Rlt_0_1 HdI) as [cI [HI _]].
  assert (Hs0 : seg a b 0 = a).
  { unfold seg. assert (RtoC 0 = C0) as H0 by (apply Ceq; simpl; lra). rewrite H0. ring. }
  assert (Hs1 : seg a b 1 = b).
  { unfold seg. assert (RtoC 1 = C1) as H1 by (apply Ceq; simpl; lra). rewrite H1. ring. }
  rewrite Hs0, Hs1 in HR, HI. apply Ceq; lra.
Qed.

Print Assumptions Cderiv0_const.
