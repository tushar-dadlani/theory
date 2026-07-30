(* ================================================================= *)
(*  FourierRsum.v  —  Rsum algebra + affine-derivative scaffolding    *)
(*  for the trigonometric-polynomial localiser (Fourier F3).          *)
(*                                                                    *)
(*  Generic, f-free toolkit reused by the modal construction:         *)
(*    • Rsum_mult_r / Rsum_ext_from1 / Rsum_telescope  (finite sums); *)
(*    • Rsum_derivable / Rsum_cont  (differentiate/continuity of a    *)
(*      finite sum termwise);                                         *)
(*    • lin_deriv : d/dt (a·t + b) = a.                               *)
(*                                                                    *)
(*  Rsum is DirichletKernel.Rsum: Rsum f n = Σ_{k=1}^{n} f(k).        *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import DirichletKernel.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Finite-sum algebra on Rsum.                                       *)
(* ----------------------------------------------------------------- *)

Lemma Rsum_mult_r : forall (f : nat -> R) (c : R) n,
  Rsum f n * c = Rsum (fun k => f k * c) n.
Proof.
  intros f c n; induction n as [| n IH]; cbn [Rsum]; [ ring | rewrite <- IH; ring ].
Qed.

(* extensionality only for the summed indices 1..n (index 0 is never used) *)
Lemma Rsum_ext_from1 : forall (f g : nat -> R) n,
  (forall k, f (S k) = g (S k)) -> Rsum f n = Rsum g n.
Proof.
  intros f g n H; induction n as [| n IH]; cbn [Rsum];
    [ reflexivity | rewrite IH, (H n); reflexivity ].
Qed.

(* telescoping: Σ_{k=1}^{n} (T k − T (k−1)) = T n − T 0 *)
Lemma Rsum_telescope : forall (T : nat -> R) n,
  Rsum (fun k => T k - T (pred k)) n = T n - T O.
Proof.
  intros T n; induction n as [| n IH]; cbn [Rsum].
  - ring.
  - change (pred (S n)) with n; rewrite IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Differentiate / continuity of a finite Rsum, termwise.           *)
(* ----------------------------------------------------------------- *)

Lemma Rsum_derivable : forall (F F' : nat -> R -> R) n y,
  (forall k, derivable_pt_lim (F k) y (F' k y)) ->
  derivable_pt_lim (fun t => Rsum (fun k => F k t) n) y (Rsum (fun k => F' k y) n).
Proof.
  intros F F' n y H; induction n as [| n IH]; cbn [Rsum].
  - apply (derivable_pt_lim_const 0).
  - apply (derivable_pt_lim_plus (fun t => Rsum (fun k => F k t) n) (F (S n)) y
             (Rsum (fun k => F' k y) n) (F' (S n) y)); [ exact IH | apply H ].
Qed.

Lemma Rsum_cont : forall (F' : nat -> R -> R) n,
  (forall k, continuity (F' k)) -> continuity (fun t => Rsum (fun k => F' k t) n).
Proof.
  intros F' n H; induction n as [| n IH]; intro y; cbn [Rsum].
  - apply continuity_pt_const; intros a b; reflexivity.
  - apply continuity_pt_plus; [ apply IH | apply H ].
Qed.

(* ----------------------------------------------------------------- *)
(*  d/dt (a·t + b) = a.                                               *)
(* ----------------------------------------------------------------- *)

Lemma lin_deriv : forall a b y, derivable_pt_lim (fun t => a * t + b) y a.
Proof.
  intros a b y.
  pose proof (derivable_pt_lim_scal id a y 1 (derivable_pt_lim_id y)) as Hs.
  pose proof (derivable_pt_lim_const b y) as Hc.
  pose proof (derivable_pt_lim_plus (mult_real_fct a id) (fct_cte b) y (a * 1) 0 Hs Hc) as Hp.
  rewrite Rmult_1_r, Rplus_0_r in Hp; exact Hp.
Qed.

Lemma lin_cont : forall a b, continuity (fun t => a * t + b).
Proof.
  intros a b y; apply continuity_pt_plus.
  - apply (continuity_pt_scal (fun t => t) a y).
    apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
  - apply continuity_pt_const; intros u v; reflexivity.
Qed.

Print Assumptions Rsum_telescope.
Print Assumptions Rsum_derivable.
Print Assumptions lin_deriv.

(* ================================================================= *)
(*  END FourierRsum.v                                                *)
(* ================================================================= *)
