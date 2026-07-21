(* ================================================================= *)
(*  HeatFlow.v                                                        *)
(*                                                                    *)
(*  DIFFUSION ON THE CUBE, DIAGONALISED BY WALSH, AND ITS EQUILIBRIUM *)
(*                                                                    *)
(*  A discrete heat / diffusion step on real signals over the Boolean *)
(*  cube F_2^3: the LAZY bit-flip walk                                *)
(*     (step f)(x) = 1/2 f(x) + 1/6 [ f(x+e0) + f(x+e1) + f(x+e2) ]   *)
(*  (stay put with prob 1/2, else move to a uniformly random          *)
(*   single-bit-flip neighbour).                                      *)
(*                                                                    *)
(*  MAIN RESULTS (real proofs; only the standard Reals axioms):       *)
(*    * step_diagonal : the Walsh-Hadamard transform DIAGONALISES the *)
(*        diffusion:  WHr (step f) y = mu y * WHr f y,                 *)
(*      with eigenvalue  mu y = 1 - |y|/3  in {1, 2/3, 1/3, 0}.        *)
(*    * iterate_spectrum : k heat steps raise each eigenvalue to the   *)
(*        k-th power:  WHr (iterate k f) y = (mu y)^k * WHr f y.       *)
(*    * mu_zero / mu_bound : the DC mode (y=0) is STATIONARY (mu=1);   *)
(*      every other mode has 0 <= mu <= 2/3 (spectral gap 1/3).        *)
(*    * dc_preserved : the total heat / spatial mean is conserved.     *)
(*    * ac_decay : every non-equilibrium Walsh mode decays,            *)
(*        |WHr (iterate k f) y| <= (2/3)^k |WHr f y|  for y <> 0.      *)
(*    * heat_equilibrium : iterate k f -> equilib f (the flat signal   *)
(*      at the spatial mean); the DC coefficient is exact at every k,  *)
(*      and the deviation on every other mode is crushed by (2/3)^k.   *)
(*                                                                    *)
(*  This is the rigorous core of: the temperature falls out of a       *)
(*  static superposition -- the diffusion damps every Walsh mode by    *)
(*  its eigenvalue, so the transient (all y<>0) dies geometrically and *)
(*  only the static DC mode -- the spatial average -- survives.        *)
(* ================================================================= *)

Require Import WalshHadamard.
From Stdlib Require Import Reals List Bool Lra.
Import ListNotations.
Open Scope R_scope.

(* We reuse from WalshHadamard: P3, mkP, c0/c1/c2, xor3, dot, allP,   *)
(* zero3.  Here the signals and transform are REAL-valued.            *)

Definition RSig := P3 -> R.

(* real character and real Walsh-Hadamard transform *)
Definition chr (a y : P3) : R := if dot a y then -1 else 1.

Definition WHr (f : RSig) : RSig :=
  fun y => fold_right Rplus 0 (map (fun x => chr x y * f x) allP).

(* the three single-bit-flip directions *)
Definition e0 : P3 := mkP true  false false.
Definition e1 : P3 := mkP false true  false.
Definition e2 : P3 := mkP false false true.

(* the lazy diffusion step *)
Definition step (f : RSig) : RSig :=
  fun x => /2 * f x + /6 * (f (xor3 x e0) + f (xor3 x e1) + f (xor3 x e2)).

(* its Walsh eigenvalue: mu y = 1/2 + 1/6 (chr e0 y + chr e1 y + chr e2 y) *)
(* which equals 1 - |y|/3 where |y| is the Hamming weight of y.         *)
Definition mu (y : P3) : R := /2 + /6 * (chr e0 y + chr e1 y + chr e2 y).

(* k iterated heat steps *)
Fixpoint iterate (k : nat) (f : RSig) : RSig :=
  match k with
  | O    => f
  | S k' => step (iterate k' f)
  end.

Ltac crush := unfold WHr, step, mu, chr, dot, xor3, e0, e1, e2, c0, c1, c2,
                     allP in *;
              cbn in *; try field; try lra; try ring.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — WALSH DIAGONALISES THE DIFFUSION                      *)
(* ----------------------------------------------------------------- *)

Theorem step_diagonal : forall f y, WHr (step f) y = mu y * WHr f y.
Proof. intros f [b0 b1 b2]; destruct b0, b1, b2; crush. Qed.

Theorem iterate_spectrum : forall k f y,
  WHr (iterate k f) y = (mu y) ^ k * WHr f y.
Proof.
  induction k as [|k' IH]; intros f y.
  - cbn [iterate pow]; ring.
  - cbn [iterate]. rewrite step_diagonal, IH. cbn [pow]. ring.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — THE SPECTRUM: STATIONARY DC MODE, CONTRACTING REST    *)
(* ----------------------------------------------------------------- *)

(* the equilibrium (DC, y=0) mode is stationary *)
Theorem mu_zero : mu zero3 = 1.
Proof. unfold mu, chr, dot, e0, e1, e2, zero3, c0, c1, c2; cbn; lra. Qed.

(* every other mode contracts: 0 <= mu y <= 2/3 (spectral gap = 1/3) *)
Theorem mu_bound : forall y, y <> zero3 -> 0 <= mu y <= 2 / 3.
Proof.
  intros y Hy; destruct y as [b0 b1 b2]; destruct b0, b1, b2;
    try (exfalso; apply Hy; reflexivity);
    unfold mu, chr, dot, e0, e1, e2, c0, c1, c2; cbn; lra.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — CONSERVATION AND DECAY                                *)
(* ----------------------------------------------------------------- *)

(* the DC coefficient (total heat = 8 * spatial mean) is conserved *)
Corollary dc_preserved : forall k f, WHr (iterate k f) zero3 = WHr f zero3.
Proof.
  intros k f; rewrite iterate_spectrum, mu_zero, pow1; ring.
Qed.

(* every non-equilibrium Walsh mode decays at least geometrically *)
Theorem ac_decay : forall k f y, y <> zero3 ->
  Rabs (WHr (iterate k f) y) <= (2 / 3) ^ k * Rabs (WHr f y).
Proof.
  intros k f y Hy.
  destruct (mu_bound y Hy) as [Hlo Hhi].
  rewrite iterate_spectrum, Rabs_mult, <- RPow_abs.
  apply Rmult_le_compat_r; [ apply Rabs_pos | ].
  apply pow_incr; split; [ apply Rabs_pos | rewrite Rabs_pos_eq; lra ].
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 4 — THE EQUILIBRIUM: THE SPATIAL MEAN                     *)
(* ----------------------------------------------------------------- *)

(* WHr f zero3 = sum_x f x ; the spatial mean is that over 8 *)
Definition mean (f : RSig) : R := / 8 * WHr f zero3.

(* the equilibrium signal: the flat distribution at the mean *)
Definition equilib (f : RSig) : RSig := fun _ => mean f.

(* the equilibrium's DC coefficient equals f's (same total heat) ... *)
Lemma WHr_equilib_dc : forall f, WHr (equilib f) zero3 = WHr f zero3.
Proof.
  intro f; unfold WHr, equilib, mean, chr, dot, zero3, c0, c1, c2, allP; cbn; field.
Qed.

(* ... and it has NO content on any other mode (character orthogonality) *)
Lemma WHr_equilib_ac : forall f y, y <> zero3 -> WHr (equilib f) y = 0.
Proof.
  intros f y Hy; destruct y as [b0 b1 b2]; destruct b0, b1, b2;
    try (exfalso; apply Hy; reflexivity);
    unfold WHr, equilib, mean, chr, dot, c0, c1, c2, allP; cbn; ring.
Qed.

(* THE EQUILIBRIUM THEOREM.                                            *)
(* On the DC mode the flow is already AT equilibrium for every k;      *)
(* on every other mode the deviation from equilibrium is crushed by    *)
(* (2/3)^k -> 0.  So iterate k f converges to equilib f = the spatial  *)
(* mean: the temperature falls out of the static superposition.        *)
Theorem heat_equilibrium : forall k f y,
  (y = zero3 -> WHr (iterate k f) y = WHr (equilib f) y)
  /\ (y <> zero3 ->
        Rabs (WHr (iterate k f) y - WHr (equilib f) y) <= (2 / 3) ^ k * Rabs (WHr f y)).
Proof.
  intros k f y; split.
  - intro Hy; subst y; rewrite dc_preserved, WHr_equilib_dc; reflexivity.
  - intro Hy; rewrite (WHr_equilib_ac f y Hy), Rminus_0_r; apply ac_decay; exact Hy.
Qed.

(* Sanity: after many steps the transient is tiny.  E.g. the slowest    *)
(* non-equilibrium mode is damped by (2/3)^k, and mu is exactly the     *)
(* stated spectrum on each Hamming shell.                               *)
Example mu_spectrum :
  mu (mkP false false false) = 1
  /\ mu (mkP true false false) = 2/3
  /\ mu (mkP true true false) = 1/3
  /\ mu (mkP true true true) = 0.
Proof.
  unfold mu, chr, dot, e0, e1, e2, c0, c1, c2; cbn; repeat split; lra.
Qed.

Print Assumptions step_diagonal.
Print Assumptions heat_equilibrium.

(* ================================================================= *)
(*  END HeatFlow.v                                                    *)
(*  The Walsh-Hadamard transform diagonalises the cube diffusion; the *)
(*  DC (spatial-mean) mode is the conserved equilibrium and every      *)
(*  other mode decays geometrically.  ZERO Admitted.                  *)
(* ================================================================= *)
