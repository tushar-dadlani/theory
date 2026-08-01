(* ================================================================= *)
(*  GammaExtend.v  —  the real Γ extended to negative arguments.      *)
(*                                                                    *)
(*  Using Γ(s+1)=s·Γ(s) (GammaRecur) in reverse, define for s > −N,   *)
(*  s ∉ {0,−1,…,−(N−1)},                                              *)
(*     GamN s N := Γ(s+N) / (s·(s+1)···(s+N−1)).                      *)
(*  This agrees with Gam on (0,∞) (GamN_pos), is independent of the   *)
(*  level N where both are defined (GamN_coherent), and satisfies the *)
(*  functional equation GamN(s+1) = s·GamN s (GamN_FE) — a Γ on all   *)
(*  of (−N,∞) minus the poles {0,−1,…}.  E.g. GamN s 1 = Γ(s+1)/s     *)
(*  extends Γ to (−1,0).                                              *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import GammaReal GammaRecur ImproperCv0 ImproperCv1.
Open Scope R_scope.

(* --- proof-irrelevance of Gam in its positivity witness --- *)

Lemma gnear_pirr : forall a c Ha Ha' Hc Hc', gnear a c Ha Hc = gnear a c Ha' Hc'.
Proof.
  intros a c Ha Ha' Hc Hc'.
  set (e := fun k => / (1 + INR k)).
  assert (He0 : forall k, 0 < e k)
    by (intro k; unfold e; apply Rinv_0_lt_compat; pose proof (pos_INR k); lra).
  assert (He1 : forall k, e k <= 1) by (intro k; unfold e; apply inv_le_1; pose proof (pos_INR k); lra).
  assert (Hecv : Un_cv e 0)
    by (unfold e; apply Un_cv_recip_0; [ intro k; pose proof (pos_INR k); lra | apply cv_infty_1_INR ]).
  apply (UL_sequence (fun k => rint01 (gnk a c) (Hf_near a c) (e k)));
    [ exact (proj2_sig (gnear_sig a c Ha Hc) e He0 He1 Hecv)
    | exact (proj2_sig (gnear_sig a c Ha' Hc') e He0 He1 Hecv) ].
Qed.

Lemma Gam_pirr : forall a Ha Hb, Gam a Ha = Gam a Hb.
Proof.
  intros a Ha Hb; unfold Gam, mellin;
    rewrite (gnear_pirr a 1 Ha Hb Rlt_0_1 Rlt_0_1); reflexivity.
Qed.

Lemma Gam_arg_eq : forall a b Ha Hb, a = b -> Gam a Ha = Gam b Hb.
Proof. intros a b Ha Hb Hab; subst b; apply Gam_pirr. Qed.

(* --- the shift product  s·(s+1)···(s+N−1) --- *)

Fixpoint prodshift (s : R) (N : nat) : R :=
  match N with O => 1 | S M => (s + INR M) * prodshift s M end.

Lemma prodshift_shift : forall s N, s * prodshift (s + 1) N = prodshift s (S N).
Proof.
  intros s N; induction N.
  - simpl; ring.
  - change (prodshift (s + 1) (S N)) with (((s + 1) + INR N) * prodshift (s + 1) N).
    change (prodshift s (S (S N))) with ((s + INR (S N)) * prodshift s (S N)).
    rewrite <- IHN, S_INR; ring.
Qed.

Lemma cancel_s : forall s x y, s <> 0 -> s * x / (s * y) = x / y.
Proof.
  intros s x y Hs; unfold Rdiv; rewrite Rinv_mult.
  replace (s * x * (/ s * / y)) with ((s * / s) * (x * / y)) by ring.
  rewrite Rinv_r by exact Hs; ring.
Qed.

(* --- the extended Gamma at level N --- *)

Definition GamN (s : R) (N : nat) (H : 0 < s + INR N) : R := Gam (s + INR N) H / prodshift s N.

Lemma GamN_pirr : forall s N H H', GamN s N H = GamN s N H'.
Proof. intros s N H H'; unfold GamN; rewrite (Gam_pirr (s + INR N) H H'); reflexivity. Qed.

Lemma GamN_agree0 : forall s (Hs : 0 < s) H, GamN s 0 H = Gam s Hs.
Proof.
  intros s Hs H; unfold GamN; cbn [prodshift]; unfold Rdiv; rewrite Rinv_1, Rmult_1_r.
  apply Gam_arg_eq; simpl; ring.
Qed.

Lemma GamN_coherent : forall s N H H', GamN s N H = GamN s (S N) H'.
Proof.
  intros s N H H'; unfold GamN; cbn [prodshift].
  assert (Hs1 : 0 < (s + INR N) + 1) by (rewrite S_INR in H'; lra).
  assert (Hrec : Gam (s + INR (S N)) H' = (s + INR N) * Gam (s + INR N) H).
  { rewrite (Gam_arg_eq (s + INR (S N)) ((s + INR N) + 1) H' Hs1 ltac:(rewrite S_INR; ring));
      apply Gam_recur. }
  rewrite Hrec; symmetry; apply cancel_s; apply Rgt_not_eq; exact H.
Qed.

Lemma GamN_pos : forall N s (Hs : 0 < s) H, GamN s N H = Gam s Hs.
Proof.
  induction N; intros s Hs H.
  - apply GamN_agree0.
  - assert (H' : 0 < s + INR N) by (pose proof (pos_INR N); lra).
    rewrite <- (GamN_coherent s N H' H); apply IHN.
Qed.

(* the functional equation on the extended domain *)
Lemma GamN_FE : forall s N H1 H, s <> 0 -> GamN (s + 1) N H1 = s * GamN s (S N) H.
Proof.
  intros s N H1 H Hs0; unfold GamN.
  rewrite (Gam_arg_eq ((s + 1) + INR N) (s + INR (S N)) H1 H ltac:(rewrite S_INR; ring)).
  rewrite <- (prodshift_shift s N),
    <- (cancel_s s (Gam (s + INR (S N)) H) (prodshift (s + 1) N) Hs0).
  unfold Rdiv; ring.
Qed.

(* Γ on (−1,0): GamN s 1 = Γ(s+1)/s, e.g. Γ(−1/2) = −2·Γ(1/2). *)
Lemma GamN_one : forall s (H : 0 < s + 1) (H1 : 0 < s + INR 1),
  GamN s 1 H1 = Gam (s + 1) H / s.
Proof.
  intros s H H1; unfold GamN; cbn [prodshift]; rewrite Rmult_1_r.
  rewrite (Gam_arg_eq (s + INR 1) (s + 1) H1 H ltac:(simpl; ring)).
  replace (s + INR 0) with s by (simpl; ring); reflexivity.
Qed.

Print Assumptions GamN_FE.

(* ================================================================= *)
(*  END GammaExtend.v.  Γ extended to (−N,∞)∖{0,−1,…} via the shift.  *)
(* ================================================================= *)
