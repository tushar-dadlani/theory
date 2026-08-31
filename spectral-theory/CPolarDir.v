(* ================================================================= *)
(*  CPolarDir.v  --  polar direction without an arg function.         *)
(*                                                                    *)
(*  There is no Clog/Carg in this development, and introducing one     *)
(*  would drag in branch choices.  Everything we need about the       *)
(*  direction of a complex number is captured by                     *)
(*                                                                    *)
(*     PosDir phi c   :=   exists r, 0 < r /\ c = Cexp phi * r        *)
(*                                                                    *)
(*  i.e. c is a POSITIVE multiple of the unit vector Cexp phi.  This   *)
(*  is closed under products (angles ADD, EulerFormula.Cexp_add) and   *)
(*  inverses, holds for x+iy with x>0 at angle atan(y/x), holds for    *)
(*  Cexpf w at angle Im w, and passes to limits.  Those five facts     *)
(*  are exactly what turns the Weierstrass product for 1/Gamma into    *)
(*  an explicit real angle given by a convergent arctan series.        *)
(*                                                                    *)
(*  phi is NOT unique (only mod 2 pi), and nothing here pretends       *)
(*  otherwise -- which is precisely why no branch has to be chosen.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra.
Require Import ComplexField Cmodulus EulerFormula CexpFull CSeries.
Open Scope R_scope.

Definition PosDir (phi : R) (c : C) : Prop :=
  exists r, 0 < r /\ c = Cmul (Cexp phi) (RtoC r).

(* ---- basic facts ---- *)

Lemma Cmod_Cexp : forall phi, Cmod (Cexp phi) = 1.
Proof.
  intro phi. unfold Cmod. rewrite Cnorm2_Cexp. apply sqrt_1.
Qed.

Lemma PosDir_C1 : PosDir 0 C1.
Proof.
  exists 1. split; [ lra | ]. rewrite Cexp_0. unfold RtoC, C1. apply Ceq; simpl; ring.
Qed.

Lemma PosDir_mul : forall a b c d,
  PosDir a c -> PosDir b d -> PosDir (a + b) (Cmul c d).
Proof.
  intros a b c d [r [Hr Hc]] [s [Hs Hd]].
  exists (r * s). split; [ apply Rmult_lt_0_compat; assumption | ].
  rewrite Hc, Hd, Cexp_add, RtoC_mul. ring.
Qed.

Lemma PosDir_mod : forall phi c, PosDir phi c -> c = Cmul (Cexp phi) (RtoC (Cmod c)).
Proof.
  intros phi c [r [Hr Hc]].
  assert (Hm : Cmod c = r).
  { rewrite Hc, Cmod_mul, Cmod_Cexp, Cmod_RtoC, Rabs_right by lra. ring. }
  rewrite Hm. exact Hc.
Qed.

Lemma PosDir_mod_pos : forall phi c, PosDir phi c -> 0 < Cmod c.
Proof.
  intros phi c [r [Hr Hc]].
  rewrite Hc, Cmod_mul, Cmod_Cexp, Cmod_RtoC, Rabs_right by lra. lra.
Qed.

Lemma PosDir_ne0 : forall phi c, PosDir phi c -> c <> C0.
Proof.
  intros phi c H E.
  pose proof (PosDir_mod_pos phi c H) as Hp.
  rewrite E in Hp. rewrite (proj2 (Cmod0 C0) eq_refl) in Hp. lra.
Qed.

Lemma RtoC_ne0' : forall r, r <> 0 -> RtoC r <> C0.
Proof.
  intros r Hr E.
  assert (Hx : Re (RtoC r) = Re C0) by (rewrite E; reflexivity).
  simpl in Hx. lra.
Qed.

Lemma Cinv_RtoC : forall r, r <> 0 -> Cinv (RtoC r) = RtoC (/ r).
Proof.
  intros r Hr. unfold Cinv, RtoC, Cnorm2; apply Ceq; cbn [Re Im]; field; lra.
Qed.

Lemma PosDir_inv : forall phi c, PosDir phi c -> PosDir (- phi) (Cinv c).
Proof.
  intros phi c [r [Hr Hc]].
  exists (/ r). split; [ apply Rinv_0_lt_compat; exact Hr | ].
  assert (Hce : Cexp phi <> C0) by apply Cexp_neq_0.
  assert (Hre : RtoC r <> C0) by (apply RtoC_ne0'; lra).
  rewrite Hc, Cexp_neg, Cconj_Cexp_is_inv, <- (Cinv_RtoC r ltac:(lra)).
  field. repeat split; assumption.
Qed.

(* the unit vector itself *)
Lemma PosDir_unit : forall phi c,
  PosDir phi c -> Cmul (Cinv (RtoC (Cmod c))) c = Cexp phi.
Proof.
  intros phi c H. destruct H as [r [Hr Hc]].
  assert (Hm : Cmod c = r).
  { rewrite Hc, Cmod_mul, Cmod_Cexp, Cmod_RtoC, Rabs_right by lra. ring. }
  assert (Hre : RtoC r <> C0) by (apply RtoC_ne0'; lra).
  rewrite Hm, Hc. field. exact Hre.
Qed.

(* ---- x + iy with x > 0 sits at angle atan (y/x) ---- *)

Lemma dir_atan : forall x y, 0 < x -> PosDir (atan (y / x)) (mkC x y).
Proof.
  intros x y Hx.
  set (a := atan (y / x)).
  assert (Hc : 0 < cos a).
  { apply cos_gt_0; destruct (atan_bound (y / x)) as [H1 H2]; unfold a; lra. }
  assert (Hs : sin a = y / x * cos a).
  { pose proof (tan_atan (y / x)) as Ht. unfold tan in Ht. fold a in Ht.
    rewrite <- Ht. field. lra. }
  exists (x / cos a). split.
  - apply Rdiv_lt_0_compat; assumption.
  - unfold Cexp, RtoC, Cmul; apply Ceq; cbn [Re Im].
    + field. lra.
    + rewrite Hs. field. lra.
Qed.

(* ---- Cexpf w sits at angle Im w ---- *)

Lemma dir_Cexpf : forall w, PosDir (Im w) (Cexpf w).
Proof.
  intro w. exists (exp (Re w)). split; [ apply exp_pos | ].
  unfold Cexpf. ring.
Qed.

(* ---- passage to the limit ---- *)

Lemma Cmod_rev : forall a b, Rabs (Cmod a - Cmod b) <= Cmod (Cminus a b).
Proof.
  intros a b.
  assert (H1 : Cmod (Cadd (Cminus a b) b) <= Cmod (Cminus a b) + Cmod b)
    by apply Cmod_triangle.
  replace (Cadd (Cminus a b) b) with a in H1 by ring.
  assert (H2 : Cmod (Cadd (Cminus b a) a) <= Cmod (Cminus b a) + Cmod a)
    by apply Cmod_triangle.
  replace (Cadd (Cminus b a) a) with b in H2 by ring.
  assert (H3 : Cmod (Cminus b a) = Cmod (Cminus a b)).
  { replace (Cminus b a) with (Copp (Cminus a b)) by ring. apply Cmod_opp. }
  rewrite H3 in H2.
  unfold Rabs; destruct (Rcase_abs (Cmod a - Cmod b)); lra.
Qed.

Lemma CUn_cv_Cmod : forall u l, CUn_cv u l -> Un_cv (fun n => Cmod (u n)) (Cmod l).
Proof.
  intros u l H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. unfold R_dist.
  eapply Rle_lt_trans; [ apply Cmod_rev | apply HN; exact Hn ].
Qed.

Lemma Un_cv_ext' : forall (u v : nat -> R) l,
  (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l He Hu eps Heps. destruct (Hu eps Heps) as [N HN].
  exists N. intros n Hn. rewrite <- (He n). apply HN; exact Hn.
Qed.

Theorem PosDir_lim : forall (u : nat -> C) (l : C) (p : nat -> R) (phi : R),
  CUn_cv u l -> Un_cv p phi -> (forall n, PosDir (p n) (u n)) ->
  l <> C0 -> PosDir phi l.
Proof.
  intros u l p phi Hu Hp Hd Hl.
  assert (Hml : 0 < Cmod l).
  { destruct (Rle_lt_or_eq_dec 0 (Cmod l) (Cmod_nonneg l)) as [H|H];
      [ exact H | exfalso; apply Hl; apply (proj1 (Cmod0 l)); symmetry; exact H ]. }
  exists (Cmod l). split; [ exact Hml | ].
  destruct (proj1 (CUn_cv_comp u l) Hu) as [Hre Him].
  assert (Hmod : Un_cv (fun n => Cmod (u n)) (Cmod l)) by (apply CUn_cv_Cmod; exact Hu).
  assert (Hcos : Un_cv (fun n => cos (p n)) (cos phi))
    by (apply continuity_seq; [ apply continuity_cos | exact Hp ]).
  assert (Hsin : Un_cv (fun n => sin (p n)) (sin phi))
    by (apply continuity_seq; [ apply continuity_sin | exact Hp ]).
  (* componentwise polar form of each u n *)
  assert (HcR : forall n, cos (p n) * Cmod (u n) = Re (u n)).
  { intro n. pose proof (PosDir_mod (p n) (u n) (Hd n)) as E.
    assert (H := f_equal Re E). unfold Cmul, Cexp, RtoC in H; cbn [Re Im] in H.
    rewrite H. ring. }
  assert (HcI : forall n, sin (p n) * Cmod (u n) = Im (u n)).
  { intro n. pose proof (PosDir_mod (p n) (u n) (Hd n)) as E.
    assert (H := f_equal Im E). unfold Cmul, Cexp, RtoC in H; cbn [Re Im] in H.
    rewrite H. ring. }
  assert (HR : Re l = cos phi * Cmod l).
  { apply (UL_sequence (fun n => Re (u n)) (Re l) (cos phi * Cmod l) Hre).
    apply (Un_cv_ext' (fun n => cos (p n) * Cmod (u n)) (fun n => Re (u n))
             (cos phi * Cmod l) HcR).
    apply CV_mult; assumption. }
  assert (HI : Im l = sin phi * Cmod l).
  { apply (UL_sequence (fun n => Im (u n)) (Im l) (sin phi * Cmod l) Him).
    apply (Un_cv_ext' (fun n => sin (p n) * Cmod (u n)) (fun n => Im (u n))
             (sin phi * Cmod l) HcI).
    apply CV_mult; assumption. }
  apply Ceq; unfold Cmul, Cexp, RtoC; cbn [Re Im]; [ rewrite HR | rewrite HI ]; ring.
Qed.

(* ---- the payoff form: Re of a product against a known direction ---- *)

Lemma PosDir_Re : forall phi c d, PosDir phi c ->
  Re (Cmul c d) = Cmod c * (cos phi * Re d - sin phi * Im d).
Proof.
  intros phi c d H.
  rewrite (PosDir_mod phi c H) at 1.
  unfold Cmul, Cexp, RtoC; cbn [Re Im]; ring.
Qed.
