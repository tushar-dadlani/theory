(* ================================================================= *)
(*  WalshUncertainty.v                                               *)
(*                                                                    *)
(*  THE DISCRETE UNCERTAINTY PRINCIPLE (Donoho-Stark) on F_2^3.       *)
(*                                                                    *)
(*  For the Walsh-Hadamard transform WH on the 8-point Boolean cube,   *)
(*  a signal and its transform cannot BOTH be concentrated:            *)
(*                                                                    *)
(*     f <> 0  ->  |supp f| * |supp (WH f)|  >=  8  ( = |F_2^3| ).     *)
(*                       (discrete_uncertainty)                       *)
(*                                                                    *)
(*  This is the finite, self-dual-group form of the Heisenberg /       *)
(*  Donoho-Stark uncertainty principle: the sharper a signal is        *)
(*  localised in "space" (small support), the more its Walsh spectrum  *)
(*  must spread out, and vice versa -- their support sizes multiply to  *)
(*  at least the size of the group.  It is the harmonic-analytic        *)
(*  COMPLEMENT of WalshSampling.v: sampling recovers a band-limited     *)
(*  signal from few samples; the uncertainty principle says WHY you     *)
(*  cannot do better -- a signal that is BOTH time- and band-limited     *)
(*  past this product bound does not exist (except f = 0).             *)
(*                                                                    *)
(*  Proof (the classical l1/l-infinity argument, here entirely over Z   *)
(*  so NO real analysis / NO axioms are needed):                      *)
(*    (A)  ||WH f||_inf <= ||f||_1           (|chi| = 1, triangle ineq) *)
(*    (B)  ||f||_1      <= |supp f| * ||f||_inf   (sum over support)    *)
(*    inversion WH(WH f) = 8 f  gives  8||f||_inf = ||WH(WH f)||_inf,   *)
(*    and chaining (A),(B) on f and on WH f, then cancelling the        *)
(*    strictly-positive ||f||_inf, yields  8 <= |supp f||supp WH f|.    *)
(*                                                                    *)
(*  Axiom-free: pure Z arithmetic on a finite group (Closed under the *)
(*  global context).                                                 *)
(* ================================================================= *)

Require Import WalshHadamard.
From Stdlib Require Import ZArith List Bool Lia Ring.
Import ListNotations.
Open Scope Z_scope.

(* every point of the cube is enumerated in allP *)
Lemma all_in : forall x, In x allP.
Proof. intros [[|] [|] [|]]; simpl; tauto. Qed.

(* ----------------------------------------------------------------- *)
(*  GENERIC LEMMAS about fold_right over Z                           *)
(* ----------------------------------------------------------------- *)

Lemma fold_max_nonneg : forall l, 0 <= fold_right Z.max 0 l.
Proof.
  induction l as [|a l IH]; simpl; [ lia | ].
  apply Z.le_trans with (fold_right Z.max 0 l); [ exact IH | apply Z.le_max_r ].
Qed.

Lemma le_fold_max : forall l v, In v l -> v <= fold_right Z.max 0 l.
Proof.
  induction l as [|a l IH]; simpl; [ contradiction | ].
  intros v [->|Hin].
  - apply Z.le_max_l.
  - apply Z.le_trans with (fold_right Z.max 0 l);
      [ apply IH; exact Hin | apply Z.le_max_r ].
Qed.

Lemma fold_max_le : forall l b,
  0 <= b -> (forall v, In v l -> v <= b) -> fold_right Z.max 0 l <= b.
Proof.
  induction l as [|a l IH]; simpl; intros b Hb Hall; [ exact Hb | ].
  apply Z.max_lub.
  - apply Hall; left; reflexivity.
  - apply IH; [ exact Hb | intros v Hv; apply Hall; right; exact Hv ].
Qed.

Lemma fold_add_nonneg : forall l,
  (forall v, In v l -> 0 <= v) -> 0 <= fold_right Z.add 0 l.
Proof.
  induction l as [|a l IH]; simpl; intros H; [ lia | ].
  assert (0 <= a) by (apply H; left; reflexivity).
  assert (0 <= fold_right Z.add 0 l) by (apply IH; intros v Hv; apply H; right; exact Hv).
  lia.
Qed.

Lemma abs_fold_add : forall l,
  Z.abs (fold_right Z.add 0 l) <= fold_right Z.add 0 (map Z.abs l).
Proof.
  induction l as [|a l IH]; simpl; [ lia | ].
  eapply Z.le_trans; [ apply Z.abs_triangle | ].
  apply Zplus_le_compat_l; exact IH.
Qed.

Lemma sum_le : forall (g h : P3 -> Z) (l : list P3),
  (forall x, In x l -> g x <= h x) ->
  fold_right Z.add 0 (map g l) <= fold_right Z.add 0 (map h l).
Proof.
  intros g h; induction l as [|a l IH]; simpl; intros Hall; [ lia | ].
  apply Zplus_le_compat.
  - apply Hall; left; reflexivity.
  - apply IH; intros x Hx; apply Hall; right; exact Hx.
Qed.

Lemma sum_mul_r : forall (g : P3 -> Z) (c : Z) (l : list P3),
  fold_right Z.add 0 (map g l) * c = fold_right Z.add 0 (map (fun x => g x * c) l).
Proof.
  intros g c; induction l as [|a l IH]; simpl; [ ring | ].
  rewrite Z.mul_add_distr_r, IH; reflexivity.
Qed.

Lemma zmax_scale : forall c a b, 0 <= c -> Z.max (c * a) (c * b) = c * Z.max a b.
Proof.
  intros c a b Hc; destruct (Z.le_ge_cases a b) as [H|H].
  - rewrite (Z.max_r a b H), Z.max_r;
      [ reflexivity | apply Z.mul_le_mono_nonneg_l; assumption ].
  - rewrite (Z.max_l a b H), Z.max_l;
      [ reflexivity | apply Z.mul_le_mono_nonneg_l; assumption ].
Qed.

Lemma fold_max_scale : forall c l, 0 <= c ->
  fold_right Z.max 0 (map (fun v => c * v) l) = c * fold_right Z.max 0 l.
Proof.
  intros c l Hc; induction l as [|a l IH]; simpl; [ ring | ].
  rewrite IH, zmax_scale; [ reflexivity | exact Hc ].
Qed.

(* ----------------------------------------------------------------- *)
(*  THE THREE NORMS (all Z-valued, all >= 0)                         *)
(*    ninf  = ||.||_inf   (max modulus)                              *)
(*    n1    = ||.||_1      (sum of moduli)                            *)
(*    ssize = |supp .|     (number of nonzero coordinates)            *)
(* ----------------------------------------------------------------- *)

Definition ninf  (f : Signal) : Z :=
  fold_right Z.max 0 (map (fun x => Z.abs (f x)) allP).
Definition n1    (f : Signal) : Z :=
  fold_right Z.add 0 (map (fun x => Z.abs (f x)) allP).
Definition ssize (f : Signal) : Z :=
  fold_right Z.add 0 (map (fun x => if Z.eqb (f x) 0 then 0 else 1) allP).

Lemma ninf_nonneg : forall f, 0 <= ninf f.
Proof. intro f; apply fold_max_nonneg. Qed.

Lemma n1_nonneg : forall f, 0 <= n1 f.
Proof.
  intro f; unfold n1; apply fold_add_nonneg.
  intros v Hv; apply in_map_iff in Hv as [x [<- _]]; apply Z.abs_nonneg.
Qed.

Lemma ssize_nonneg : forall f, 0 <= ssize f.
Proof.
  intro f; unfold ssize; apply fold_add_nonneg.
  intros v Hv; apply in_map_iff in Hv as [x [<- _]]; destruct (Z.eqb (f x) 0); lia.
Qed.

(* each coordinate modulus is <= the max modulus *)
Lemma le_ninf : forall f x, Z.abs (f x) <= ninf f.
Proof.
  intros f x; apply le_fold_max, (in_map (fun x0 => Z.abs (f x0))), all_in.
Qed.

(* nonzero signal has strictly positive sup-norm *)
Lemma ninf_pos : forall f x, f x <> 0 -> 0 < ninf f.
Proof.
  intros f x Hx; apply Z.lt_le_trans with (Z.abs (f x)).
  - apply (proj2 (Z.abs_pos (f x))); exact Hx.
  - apply le_ninf.
Qed.

(* ----------------------------------------------------------------- *)
(*  (A)  ||WH f||_inf <= ||f||_1     (|chi| = 1 + triangle inequality) *)
(* ----------------------------------------------------------------- *)

Lemma ninf_WH_le_n1 : forall f, ninf (WH f) <= n1 f.
Proof.
  intro f; unfold ninf.
  apply fold_max_le; [ apply n1_nonneg | ].
  intros v Hv; apply in_map_iff in Hv as [y [<- _]].
  unfold WH, n1.
  eapply Z.le_trans; [ apply abs_fold_add | ].
  rewrite map_map.
  apply sum_le; intros x _.
  rewrite Z.abs_mul.
  replace (Z.abs (chi x y)) with 1
    by (unfold chi, signb; destruct (dot x y); reflexivity).
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  (B)  ||f||_1 <= |supp f| * ||f||_inf   (sum over the support)     *)
(* ----------------------------------------------------------------- *)

Lemma n1_le : forall f, n1 f <= ssize f * ninf f.
Proof.
  intro f; unfold n1, ssize; rewrite sum_mul_r.
  apply sum_le; intros x _.
  destruct (Z.eqb (f x) 0) eqn:E.
  - apply Z.eqb_eq in E; rewrite E; simpl; lia.
  - rewrite Z.mul_1_l; apply le_ninf.
Qed.

(* ----------------------------------------------------------------- *)
(*  INVERSION:  8 * ||f||_inf = ||WH (WH f)||_inf                     *)
(*  (WH(WH f) = 8 f pointwise, and the sup-norm scales by 8)          *)
(* ----------------------------------------------------------------- *)

Lemma ninf_ext : forall f g, (forall x, f x = g x) -> ninf f = ninf g.
Proof. intros f g H; unfold ninf; f_equal; apply map_ext; intro x; rewrite H; reflexivity. Qed.

Lemma ninf_WHWH : forall f, ninf (WH (WH f)) = 8 * ninf f.
Proof.
  intro f.
  rewrite (ninf_ext (WH (WH f)) (fun x => 8 * f x)) by (intro x; apply WH_involution).
  unfold ninf.
  rewrite (map_ext (fun x => Z.abs (8 * f x)) (fun x => 8 * Z.abs (f x)))
    by (intro x; rewrite Z.abs_mul; reflexivity).
  rewrite <- (map_map (fun x => Z.abs (f x)) (fun v => 8 * v)).
  apply fold_max_scale; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE UNCERTAINTY PRINCIPLE                                        *)
(* ----------------------------------------------------------------- *)

Theorem discrete_uncertainty : forall f,
  (exists x, f x <> 0) -> 8 <= ssize f * ssize (WH f).
Proof.
  intros f [x0 Hx0].
  assert (Hpos : 0 < ninf f) by (apply ninf_pos with x0; exact Hx0).
  (* 8||f||inf = ||WH WH f||inf <= ||WH f||1 <= |supp WH f|*||WH f||inf   *)
  (*            <= |supp WH f| * (|supp f| * ||f||inf)                    *)
  assert (Hchain : 8 * ninf f <= ssize (WH f) * ssize f * ninf f).
  { rewrite <- ninf_WHWH.
    eapply Z.le_trans; [ apply ninf_WH_le_n1 | ].
    eapply Z.le_trans; [ apply n1_le | ].
    rewrite <- Z.mul_assoc.
    apply Z.mul_le_mono_nonneg_l; [ apply ssize_nonneg | ].
    eapply Z.le_trans; [ apply ninf_WH_le_n1 | apply n1_le ]. }
  (* cancel the strictly positive ||f||_inf *)
  rewrite Z.mul_comm.
  apply (proj2 (Z.mul_le_mono_pos_r 8 (ssize (WH f) * ssize f) (ninf f) Hpos)).
  exact Hchain.
Qed.

Print Assumptions discrete_uncertainty.

(* ================================================================= *)
(*  END WalshUncertainty.v                                           *)
(*  The Donoho-Stark discrete uncertainty principle on F_2^3:         *)
(*  a nonzero signal and its Walsh-Hadamard transform have support     *)
(*  sizes whose product is at least |F_2^3| = 8.  The finite, self-    *)
(*  dual-group, complex-analysis-free form of Heisenberg uncertainty,  *)
(*  and the complement to WalshSampling's reconstruction theorem.      *)
(*  ZERO Admitted; Closed under the global context.                   *)
(* ================================================================= *)
