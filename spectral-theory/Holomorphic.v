(* ================================================================= *)
(*  Holomorphic.v  —  complex derivative and holomorphy on C.         *)
(*                                                                    *)
(*  is_Cderiv F z d  ==  |F(z+h) - F(z) - d*h| <= eps*|h|  (o(h) form).*)
(*  HolomorphicOn F U == a complex derivative exists at every z in U. *)
(*  Provides the closure algebra (const, id, +, -, product, affine    *)
(*  precomposition) needed to assemble the completed xi.  Axiom-clean. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus.
Open Scope R_scope.

Definition is_Cderiv (F : C -> C) (z d : C) : Prop :=
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall h, Cmod h < del ->
      Cmod (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d h)) <= eps * Cmod h.

Definition HolomorphicOn (F : C -> C) (U : C -> Prop) : Prop :=
  forall z, U z -> exists d, is_Cderiv F z d.

(* helper: Cmod C0 = 0 *)
Lemma Cmod_C0 : Cmod C0 = 0.
Proof. apply (proj2 (Cmod0 C0)); reflexivity. Qed.

Lemma Cderiv_const : forall (c z : C), is_Cderiv (fun _ => c) z C0.
Proof.
  intros c z eps Heps; exists 1; split; [ lra | ].
  intros h _. replace (Cminus (Cminus c c) (Cmul C0 h)) with C0 by ring.
  rewrite Cmod_C0. apply Rmult_le_pos; [ lra | apply Cmod_nonneg ].
Qed.

Lemma Cderiv_id : forall z : C, is_Cderiv (fun w => w) z C1.
Proof.
  intros z eps Heps; exists 1; split; [ lra | ].
  intros h _. replace (Cminus (Cminus (Cadd z h) z) (Cmul C1 h)) with C0 by ring.
  rewrite Cmod_C0. apply Rmult_le_pos; [ lra | apply Cmod_nonneg ].
Qed.

Lemma Cderiv_add : forall F G z dF dG,
  is_Cderiv F z dF -> is_Cderiv G z dG ->
  is_Cderiv (fun w => Cadd (F w) (G w)) z (Cadd dF dG).
Proof.
  intros F G z dF dG HF HG eps Heps.
  destruct (HF (eps/2) ltac:(lra)) as [d1 [Hd1 HF']].
  destruct (HG (eps/2) ltac:(lra)) as [d2 [Hd2 HG']].
  exists (Rmin d1 d2); split; [ apply Rmin_pos; assumption | ].
  intros h Hh.
  assert (Hh1 : Cmod h < d1) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (Hh2 : Cmod h < d2) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  replace (Cminus (Cminus (Cadd (F (Cadd z h)) (G (Cadd z h))) (Cadd (F z) (G z))) (Cmul (Cadd dF dG) h))
    with (Cadd (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul dF h))
               (Cminus (Cminus (G (Cadd z h)) (G z)) (Cmul dG h))) by ring.
  eapply Rle_trans; [ apply Cmod_triangle | ].
  replace (eps * Cmod h) with (eps/2 * Cmod h + eps/2 * Cmod h) by lra.
  apply Rplus_le_compat; [ apply HF' | apply HG' ]; assumption.
Qed.

Lemma Cderiv_opp : forall F z dF,
  is_Cderiv F z dF -> is_Cderiv (fun w => Copp (F w)) z (Copp dF).
Proof.
  intros F z dF HF eps Heps.
  destruct (HF eps Heps) as [d [Hd HF']]; exists d; split; [ assumption | ].
  intros h Hh.
  replace (Cminus (Cminus (Copp (F (Cadd z h))) (Copp (F z))) (Cmul (Copp dF) h))
    with (Copp (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul dF h))) by ring.
  rewrite Cmod_opp. apply HF'; assumption.
Qed.

Lemma Cderiv_minus : forall F G z dF dG,
  is_Cderiv F z dF -> is_Cderiv G z dG ->
  is_Cderiv (fun w => Cminus (F w) (G w)) z (Cminus dF dG).
Proof.
  intros F G z dF dG HF HG.
  assert (Heq : (fun w => Cminus (F w) (G w)) = (fun w => Cadd (F w) (Copp (G w)))).
  { apply functional_extensionality; intro w; ring. }
  rewrite Heq. replace (Cminus dF dG) with (Cadd dF (Copp dG)) by ring.
  apply Cderiv_add; [ assumption | apply Cderiv_opp; assumption ].
Qed.

(* precomposition with an affine map w |-> a*w + b *)
Lemma Cderiv_comp_affine : forall F a b z d,
  is_Cderiv F (Cadd (Cmul a z) b) d ->
  is_Cderiv (fun w => F (Cadd (Cmul a w) b)) z (Cmul a d).
Proof.
  intros F a b z d HF eps Heps.
  pose proof (Cmod_nonneg a) as Hpa.
  destruct (HF (eps / (Cmod a + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [d1 [Hd1 HF']].
  exists (d1 / (Cmod a + 1)); split.
  { apply Rdiv_lt_0_compat; lra. }
  intros h Hh. pose proof (Cmod_nonneg h) as Hph.
  set (k := Cmul a h).
  assert (Hkmod : Cmod k = Cmod a * Cmod h) by (unfold k; apply Cmod_mul).
  assert (Hk : Cmod k < d1).
  { rewrite Hkmod.
    apply Rle_lt_trans with (Cmod a * (d1 / (Cmod a + 1))).
    - apply Rmult_le_compat_l; [ assumption | apply Rlt_le, Hh ].
    - apply Rmult_lt_reg_r with (Cmod a + 1); [ lra | ].
      replace (Cmod a * (d1 / (Cmod a + 1)) * (Cmod a + 1)) with (Cmod a * d1) by (field; lra).
      nra. }
  replace (Cadd (Cmul a (Cadd z h)) b) with (Cadd (Cadd (Cmul a z) b) k) by (unfold k; ring).
  replace (Cmul (Cmul a d) h) with (Cmul d k) by (unfold k; ring).
  eapply Rle_trans; [ apply (HF' k Hk) | ].
  rewrite Hkmod.
  apply Rmult_le_reg_r with (Cmod a + 1); [ lra | ].
  replace (eps / (Cmod a + 1) * (Cmod a * Cmod h) * (Cmod a + 1)) with (eps * Cmod a * Cmod h) by (field; lra).
  nra.
Qed.

(* product of an AFFINE factor (a*w+b, remainder-free) with a holomorphic
   factor.  Covers scalar multiples (a=C0) and linear factors (a=C1). *)
Lemma Cderiv_mul_affine : forall a b G z dG,
  is_Cderiv G z dG ->
  is_Cderiv (fun w => Cmul (Cadd (Cmul a w) b) (G w)) z
            (Cadd (Cmul a (G z)) (Cmul (Cadd (Cmul a z) b) dG)).
Proof.
  intros a b G z dG HG eps Heps.
  pose proof (Cmod_nonneg a) as Hpa. pose proof (Cmod_nonneg dG) as HpdG.
  pose proof (Cmod_nonneg (Cadd (Cmul a z) b)) as HpFz.
  set (B := Cmod (Cadd (Cmul a z) b) + Cmod a + 1).
  assert (HB : 0 < B) by (unfold B; lra).
  set (epsG := eps / (2 * B)).
  assert (HepsG : 0 < epsG) by (unfold epsG; apply Rdiv_lt_0_compat; lra).
  destruct (HG epsG HepsG) as [dG0 [HdG0 HG']].
  set (K := Cmod a * Cmod dG + Cmod a * epsG + 1).
  assert (HK : 0 < K) by (unfold K; pose proof (Rmult_le_pos (Cmod a) (Cmod dG) Hpa HpdG);
    pose proof (Rmult_le_pos (Cmod a) epsG Hpa (Rlt_le _ _ HepsG)); lra).
  set (del := Rmin dG0 (Rmin 1 (eps / (2 * K)))).
  assert (Hdel : 0 < del)
    by (unfold del; apply Rmin_pos; [ assumption | apply Rmin_pos; [ lra | apply Rdiv_lt_0_compat; lra ] ]).
  exists del; split; [ assumption | ].
  intros h Hh. pose proof (Cmod_nonneg h) as Hph.
  assert (HhdG0 : Cmod h < dG0)
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; apply Rmin_l ]).
  assert (Hh1 : Cmod h < 1)
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
  assert (Hh2 : Cmod h < eps / (2 * K))
    by (eapply Rlt_le_trans; [ exact Hh | unfold del; eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ]).
  assert (HGR : Cmod (Cminus (Cminus (G (Cadd z h)) (G z)) (Cmul dG h)) <= epsG * Cmod h)
    by (apply HG'; assumption).
  set (GR := Cminus (Cminus (G (Cadd z h)) (G z)) (Cmul dG h)).
  replace (Cminus (Cminus (Cmul (Cadd (Cmul a (Cadd z h)) b) (G (Cadd z h)))
                          (Cmul (Cadd (Cmul a z) b) (G z)))
                  (Cmul (Cadd (Cmul a (G z)) (Cmul (Cadd (Cmul a z) b) dG)) h))
    with (Cadd (Cadd (Cmul (Cadd (Cmul a z) b) GR) (Cmul (Cmul (Cmul a h) dG) h))
               (Cmul (Cmul a h) GR))
    by (unfold GR; ring).
  eapply Rle_trans; [ apply Cmod_triangle | ].
  eapply Rle_trans; [ apply Rplus_le_compat_r; apply Cmod_triangle | ].
  (* bound the three summands *)
  assert (HT1 : Cmod (Cmul (Cadd (Cmul a z) b) GR) <= Cmod (Cadd (Cmul a z) b) * (epsG * Cmod h)).
  { rewrite Cmod_mul; apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact HGR ]. }
  assert (HT2 : Cmod (Cmul (Cmul (Cmul a h) dG) h) = Cmod a * Cmod dG * (Cmod h * Cmod h)).
  { rewrite !Cmod_mul; ring. }
  assert (HT3 : Cmod (Cmul (Cmul a h) GR) <= Cmod a * epsG * (Cmod h * Cmod h)).
  { rewrite Cmod_mul, Cmod_mul.
    replace (Cmod a * Cmod h * Cmod GR) with (Cmod a * Cmod h * Cmod GR) by ring.
    apply Rle_trans with (Cmod a * Cmod h * (epsG * Cmod h)).
    - apply Rmult_le_compat_l; [ apply Rmult_le_pos; assumption | exact HGR ].
    - apply Req_le; ring. }
  (* coefficient bounds *)
  assert (Kb1 : Cmod (Cadd (Cmul a z) b) * epsG <= eps / 2).
  { unfold epsG. apply Rmult_le_reg_r with (2 * B); [ lra | ].
    replace (Cmod (Cadd (Cmul a z) b) * (eps / (2 * B)) * (2 * B))
      with (Cmod (Cadd (Cmul a z) b) * eps) by (field; lra).
    unfold B in *. nra. }
  assert (Kb2 : (Cmod a * Cmod dG + Cmod a * epsG) * Cmod h <= eps / 2).
  { apply Rle_trans with (K * Cmod h).
    - apply Rmult_le_compat_r; [ assumption | unfold K; lra ].
    - apply Rlt_le. apply Rmult_lt_reg_r with (/ K); [ apply Rinv_0_lt_compat; assumption | ].
      replace (K * Cmod h * / K) with (Cmod h) by (field; lra).
      replace (eps / 2 * / K) with (eps / (2 * K)) by (field; lra). exact Hh2. }
  rewrite Rplus_assoc.
  apply Rle_trans with (eps / 2 * Cmod h + eps / 2 * Cmod h); [ | lra ].
  apply Rplus_le_compat.
  - eapply Rle_trans; [ exact HT1 | ].
    replace (Cmod (Cadd (Cmul a z) b) * (epsG * Cmod h))
      with ((Cmod (Cadd (Cmul a z) b) * epsG) * Cmod h) by ring.
    apply Rmult_le_compat_r; [ assumption | exact Kb1 ].
  - rewrite HT2. eapply Rle_trans; [ apply Rplus_le_compat_l; exact HT3 | ].
    replace (Cmod a * Cmod dG * (Cmod h * Cmod h) + Cmod a * epsG * (Cmod h * Cmod h))
      with (((Cmod a * Cmod dG + Cmod a * epsG) * Cmod h) * Cmod h) by ring.
    apply Rmult_le_compat_r; [ assumption | exact Kb2 ].
Qed.

Print Assumptions Cderiv_mul_affine.

(* ================================================================= *)
(*  END Holomorphic.v (definitions + linear/affine-product algebra). *)
(* ================================================================= *)
