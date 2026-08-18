(* ================================================================= *)
(*  PrimorialGrid.v  —  the primorial as a hyperfinite integration grid. *)
(*                                                                    *)
(*  Read dx k = 1/primorial k as the INFINITESIMAL cell width and         *)
(*  primorial k as the CELL COUNT / total extent N = 1/dx.  Then:         *)
(*                                                                    *)
(*    dx k . primorial k = 1              (the N cells tile [0,1];        *)
(*                                         width . count = unit measure)  *)
(*    (dx k)^n . (primorial k)^n = 1      (n-dim: infinitesimal volume    *)
(*                                         element dx^n times N^n cells    *)
(*                                         = unit n-cube volume)          *)
(*    dx k -> 0                           ((1/primorial)^inf: infinitesimal*)
(*    primorial k -> +inf                 (primorial^inf: total extent)   *)
(*    (dx k)^(S n) = (dx k)^n . dx k      (higher-order infinitesimals)   *)
(*                                                                    *)
(*  So (1/primorial)^n is an n-th-order infinitesimal volume element and  *)
(*  (primorial)^n the matching n-dimensional cell count -- their product  *)
(*  is the unit domain of an n-fold integral.  This is the primorial      *)
(*  hyperfinite (Loeb-style) grid; the sieve density phi(primorial)/      *)
(*  primorial is the measure of the coprime (reduced-residue) points.     *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import CountTwoCollapse.
Open Scope R_scope.

Section Grid.
Variable P : nat -> R.                 (* abstract prime enumeration *)
Hypothesis HP : forall i, 2 <= P i.    (* each prime is >= 2 *)

Fixpoint primorial (k : nat) : R :=
  match k with 0 => 1 | S k' => primorial k' * P k' end.

Definition dx (k : nat) : R := / primorial k.   (* the infinitesimal cell width *)

Lemma primorial_pos : forall k, 0 < primorial k.
Proof.
  induction k as [| k IH]; simpl; [ lra | ].
  apply Rmult_lt_0_compat; [ exact IH | pose proof (HP k); lra ].
Qed.

Lemma primorial_ge_pow2 : forall k, 2 ^ k <= primorial k.
Proof.
  induction k as [| k IH]; simpl; [ lra | ].
  apply Rle_trans with (2 ^ k * 2).
  - lra.
  - apply Rmult_le_compat; [ apply pow_le; lra | lra | exact IH | apply HP ].
Qed.

(* width . count = 1 : the N cells of width dx tile the unit interval *)
Theorem grid_unit : forall k, dx k * primorial k = 1.
Proof.
  intro k. unfold dx. rewrite Rinv_l; [ reflexivity | ].
  pose proof (primorial_pos k); lra.
Qed.

(* n-dimensional: (dx)^n . N^n = 1, the volume of the unit n-cube *)
Theorem grid_unit_n : forall n k, (dx k) ^ n * (primorial k) ^ n = 1.
Proof.
  intros n k. induction n as [| n IH]; simpl; [ ring | ].
  replace (dx k * dx k ^ n * (primorial k * primorial k ^ n))
    with ((dx k * primorial k) * (dx k ^ n * primorial k ^ n)) by ring.
  rewrite grid_unit, IH. ring.
Qed.

(* dx -> 0 : the infinitesimal (sub-geometric: dx k <= (1/2)^k) *)
Theorem dx_cv0 : Un_cv dx 0.
Proof.
  intros eps Heps. destruct (inv2_pow_cv0 eps Heps) as [N HN]. exists N. intros n Hn.
  specialize (HN n Hn). unfold R_dist in *. rewrite Rminus_0_r in *. unfold dx.
  assert (H1 : 0 <= / primorial n) by (apply Rlt_le, Rinv_0_lt_compat, primorial_pos).
  assert (H2 : / primorial n <= (/ 2) ^ n).
  { rewrite <- Rinv_pow by lra.
    apply Rinv_le_contravar; [ apply pow_lt; lra | apply primorial_ge_pow2 ]. }
  assert (H3 : 0 <= (/ 2) ^ n) by (apply pow_le; lra).
  rewrite Rabs_right in HN by (apply Rle_ge; exact H3).
  rewrite Rabs_right by (apply Rle_ge; exact H1). lra.
Qed.

(* N -> +infinity : the total extent *)
Theorem extent_cv_infty : cv_infty primorial.
Proof.
  intro M. destruct (pow2_cv_infty M) as [N HN]. exists N. intros n Hn.
  pose proof (primorial_ge_pow2 n). pose proof (HN n Hn). lra.
Qed.

(* higher-order infinitesimals: each order is the previous times dx *)
Lemma dx_higher_order : forall n k, (dx k) ^ (S n) = (dx k) ^ n * dx k.
Proof. intros n k; simpl; ring. Qed.

(* ===== the integration-grid duality, bundled ===== *)
Theorem primorial_grid :
  (forall k, dx k * primorial k = 1)                      (* width . count = unit measure *)
  /\ (forall n k, (dx k) ^ n * (primorial k) ^ n = 1)     (* dx^n . N^n = unit n-volume *)
  /\ Un_cv dx 0                                            (* (1/primorial)^inf: infinitesimal *)
  /\ cv_infty primorial                                   (* primorial^inf: total extent *)
  /\ (forall n k, (dx k) ^ (S n) = (dx k) ^ n * dx k).    (* higher-order infinitesimals *)
Proof.
  split; [ exact grid_unit | ].
  split; [ exact grid_unit_n | ].
  split; [ exact dx_cv0 | ].
  split; [ exact extent_cv_infty | exact dx_higher_order ].
Qed.

End Grid.

Print Assumptions grid_unit_n.
Print Assumptions primorial_grid.
