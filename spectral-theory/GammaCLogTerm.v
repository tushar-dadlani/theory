(* ================================================================= *)
(*  GammaCLogTerm.v   (the complex log-derivative term and its primitive) *)
(*                                                                    *)
(*  For the GammaC != 0 holomorphy brick (Route B, exp(L) form).         *)
(*  The n-th log-derivative term  t_n(z) = log(1+z/(n+1)) - z/(n+1)  is   *)
(*  built as the complex PRIMITIVE of its own derivative                 *)
(*     gterm n z = 1/((n+1)+z) - 1/(n+1)  (= -z/((n+1)((n+1)+z)))         *)
(*  on the convex open region  U = { Re z > -1/2 }, via CPrimConv.PrimC.  *)
(*  Since PrimC needs a GLOBALLY continuous integrand (CcontC), gterm is   *)
(*  clamped to ghat (Re clamped to >= -1/2), which agrees with gterm on U.*)
(*                                                                    *)
(*     tterm_deriv : is_Cderiv (tterm n) z (gterm n z)   for Re z > -1/2; *)
(*     tterm_0     : tterm n C0 = C0;                                    *)
(*     gterm_deriv : is_Cderiv (gterm n) z (dgterm n z);                 *)
(*     Cmod_dgterm_le : Cmod (dgterm n z) <= /(INR (S n))^2  (Re z >= 0). *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (+ functional_extensionality). *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSegInt CIntegral2 CWindingOffCenter CImproperIntegral
        Holomorphic CDeriv CHoloCalculus CPrimConv CZetaDeriv2 CTruncDisk CSeries
        PerronRemovable.
Open Scope R_scope.

Lemma Snpos : forall n, 1 <= INR (S n).
Proof. intro n. rewrite <- INR_1. apply le_INR. lia. Qed.

(* the region  U = { Re z > -1/2 } *)
Definition RG (z : C) : Prop := - / 2 < Re z.

Lemma RG_C0 : RG C0.
Proof. unfold RG, C0; cbn [Re]; lra. Qed.

Lemma RG_convex : Convex RG.
Proof.
  intros a b Ha Hb s Hs. unfold RG in *. rewrite Re_seg.
  destruct Hs as [Hs0 Hs1].
  destruct (Req_dec s 0) as [-> | Hne]; [ lra | ].
  assert (0 < s * (Re b + / 2)) by (apply Rmult_lt_0_compat; lra).
  assert (0 <= (1 - s) * (Re a + / 2)) by (apply Rmult_le_pos; lra).
  nra.
Qed.

Lemma RG_open : Open RG.
Proof.
  intros z Hz. unfold RG in *. exists (Re z + / 2). split; [ lra | ].
  intros w Hw. pose proof (Cmod_Re_le (Cminus w z)) as HR.
  rewrite Re_Cminus in HR.
  pose proof (Rabs_Ropp (Re w - Re z)). pose proof (Rle_abs (- (Re w - Re z))). lra.
Qed.

(* the term's derivative  gterm  and its derivative  dgterm *)
Definition gterm (n : nat) (z : C) : C :=
  Cminus (Cinv (Cadd (RtoC (INR (S n))) z)) (RtoC (/ INR (S n))).
Definition dgterm (n : nat) (z : C) : C :=
  Copp (Cinv (Cmul (Cadd (RtoC (INR (S n))) z) (Cadd (RtoC (INR (S n))) z))).

Lemma kz_ne0 : forall n z, RG z -> Cadd (RtoC (INR (S n))) z <> C0.
Proof.
  intros n z Hz Hc. apply (f_equal Re) in Hc.
  unfold Cadd, RtoC, C0, RG in *; cbn [Re] in *. pose proof (Snpos n). lra.
Qed.

Lemma gterm_deriv : forall n z, RG z -> is_Cderiv (gterm n) z (dgterm n z).
Proof.
  intros n z Hz.
  assert (HG : is_Cderiv (fun w => Cadd (RtoC (INR (S n))) w) z C1).
  { apply (is_Cderiv_eq _ _ (Cadd C0 C1));
      [ apply Cderiv_add; [ apply Cderiv_const | apply Cderiv_id ] | ring ]. }
  assert (H : is_Cderiv (gterm n) z
    (Cminus (Cmul (Copp (Cinv (Cmul (Cadd (RtoC (INR (S n))) z)
                                    (Cadd (RtoC (INR (S n))) z)))) C1) C0)).
  { unfold gterm. apply Cderiv_minus.
    - apply (Cderiv_invc (fun w => Cadd (RtoC (INR (S n))) w) z C1 HG (kz_ne0 n z Hz)).
    - apply Cderiv_const. }
  apply (is_Cderiv_eq _ _ _ (dgterm n z) H). unfold dgterm.
  set (X := Copp (Cinv (Cmul (Cadd (RtoC (INR (S n))) z) (Cadd (RtoC (INR (S n))) z)))).
  ring.
Qed.

Lemma Cmod_dgterm_le : forall n z, 0 <= Re z -> Cmod (dgterm n z) <= / (INR (S n)) ^ 2.
Proof.
  intros n z Hz. pose proof (Snpos n) as HS.
  assert (Hk : INR (S n) <= Cmod (Cadd (RtoC (INR (S n))) z)).
  { apply Rle_trans with (Re (Cadd (RtoC (INR (S n))) z)).
    - unfold Cadd, RtoC; cbn [Re]. lra.
    - eapply Rle_trans; [ apply Rle_abs | apply Cmod_Re_le ]. }
  assert (HCk : 0 < Cmod (Cadd (RtoC (INR (S n))) z)) by lra.
  assert (Hkk : Cmul (Cadd (RtoC (INR (S n))) z) (Cadd (RtoC (INR (S n))) z) <> C0).
  { intro Hc. assert (H0 : Cmod (Cmul (Cadd (RtoC (INR (S n))) z)
                                      (Cadd (RtoC (INR (S n))) z)) = 0)
      by (rewrite Hc; apply (proj2 (Cmod0 C0)); reflexivity).
    rewrite Cmod_mul in H0. nra. }
  unfold dgterm. rewrite Cmod_opp, (Cmod_inv _ Hkk), Cmod_mul.
  replace (/ (INR (S n)) ^ 2) with (/ (INR (S n) * INR (S n))) by (f_equal; simpl; ring).
  apply Rinv_le_contravar; [ apply Rmult_lt_0_compat; lra | ].
  apply Rmult_le_compat; lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  the globally-continuous clamp  ghat = gterm on U                   *)
(* ------------------------------------------------------------------ *)

Definition cl (w : C) : C := mkC (Rmax (Re w) (- / 2)) (Im w).
Definition ghat (n : nat) (w : C) : C :=
  Cminus (Cinv (Cadd (RtoC (INR (S n))) (cl w))) (RtoC (/ INR (S n))).

Lemma cl_id : forall w, - / 2 < Re w -> cl w = w.
Proof.
  intros w Hw. unfold cl. apply Ceq; cbn [Re Im]; [ apply Rmax_left; lra | reflexivity ].
Qed.

Lemma ghat_eq_gterm : forall n w, RG w -> ghat n w = gterm n w.
Proof. intros n w Hw. unfold ghat, gterm. rewrite (cl_id w Hw). reflexivity. Qed.

Lemma Ccont_minus : forall f g, Ccont f -> Ccont g -> Ccont (fun u => Cminus (f u) (g u)).
Proof.
  intros f g [HRf HIf] [HRg HIg]. split.
  - assert (Heq : (fun u => Re (Cminus (f u) (g u))) = (fun u => Re (f u) - Re (g u)))
      by (apply functional_extensionality; intro u; reflexivity).
    rewrite Heq. apply continuity_minus; assumption.
  - assert (Heq : (fun u => Im (Cminus (f u) (g u))) = (fun u => Im (f u) - Im (g u)))
      by (apply functional_extensionality; intro u; reflexivity).
    rewrite Heq. apply continuity_minus; assumption.
Qed.

Lemma cont_cl : forall g : R -> C, Ccont g -> Ccont (fun u => cl (g u)).
Proof.
  intros g [HRe HIm]. split.
  - assert (Heq : (fun u => Re (cl (g u))) = (fun u => Rmax (Re (g u) + / 2) 0 - / 2)).
    { apply functional_extensionality; intro u. unfold cl; cbn [Re]. unfold Rmax.
      destruct (Rle_dec (Re (g u)) (- / 2)); destruct (Rle_dec (Re (g u) + / 2) 0); lra. }
    rewrite Heq. apply continuity_minus.
    + apply cont_max0. apply continuity_plus;
        [ exact HRe | intro x; apply continuity_pt_const; intros a b; reflexivity ].
    + intro x; apply continuity_pt_const; intros a b; reflexivity.
  - assert (Heq : (fun u => Im (cl (g u))) = (fun u => Im (g u)))
      by (apply functional_extensionality; intro u; reflexivity).
    rewrite Heq; exact HIm.
Qed.

Lemma denom_ne0 : forall n w, Cadd (RtoC (INR (S n))) (cl w) <> C0.
Proof.
  intros n w Hc. apply (f_equal Re) in Hc.
  unfold Cadd, RtoC, C0, cl in Hc; cbn [Re] in Hc.
  pose proof (Snpos n). pose proof (Rmax_r (Re w) (- / 2)). lra.
Qed.

Lemma ghat_cc : forall n, CcontC (ghat n).
Proof.
  intros n g Hg. unfold ghat. apply Ccont_minus.
  - apply Ccont_inv.
    + apply Ccont_add; [ apply Ccont_const | apply cont_cl; exact Hg ].
    + intro u. apply denom_ne0.
  - apply Ccont_const.
Qed.

Lemma ghat_hol : forall n z, RG z -> exists d, is_Cderiv (ghat n) z d.
Proof.
  intros n z Hz. destruct (RG_open z Hz) as [r [Hr Hball]].
  exists (dgterm n z).
  apply (is_Cderiv_congr (ghat n) (gterm n) z (dgterm n z) r Hr).
  - intros w Hw. apply ghat_eq_gterm. apply Hball; exact Hw.
  - apply gterm_deriv; exact Hz.
Qed.

(* ------------------------------------------------------------------ *)
(*  the primitive  tterm = PrimC ghat  and its derivative              *)
(* ------------------------------------------------------------------ *)

Definition tterm (n : nat) : C -> C := PrimC (ghat n) (ghat_cc n) C0.

Theorem tterm_deriv : forall n z, RG z -> is_Cderiv (tterm n) z (gterm n z).
Proof.
  intros n z Hz. unfold tterm.
  apply (is_Cderiv_eq _ _ (ghat n z) (gterm n z)).
  - exact (PrimC_deriv RG RG_convex RG_open (ghat n) (ghat_cc n)
             (ghat_hol n) C0 RG_C0 z Hz).
  - apply ghat_eq_gterm; exact Hz.
Qed.

Theorem tterm_0 : forall n, tterm n C0 = C0.
Proof. intro n. unfold tterm, PrimC. apply seg_int_self. Qed.

Print Assumptions tterm_deriv.
