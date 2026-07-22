(* ================================================================= *)
(*  HeatFlowQ.v                                                       *)
(*                                                                    *)
(*  The diffusion diagonalised by Walsh + equilibrium, over Q --      *)
(*  the axiom-free rational version of HeatFlow.v.  Reuses the F_2^3   *)
(*  combinatorics from WalshHadamard.v; all eigenvalues are rational   *)
(*  ({1, 2/3, 1/3, 0}), so no Reals are needed.                       *)
(* ================================================================= *)

Require Import WalshHadamard.
From Stdlib Require Import QArith Qabs Lqa Bool List.
Import ListNotations.
Open Scope Q_scope.

Definition RSigQ := P3 -> Q.
Definition chrq (a y : P3) : Q := if dot a y then -1 else 1.

Definition WHq (f : RSigQ) : RSigQ :=
  fun y => fold_right Qplus 0 (map (fun x => chrq x y * f x) allP).

Definition e0 : P3 := mkP true  false false.
Definition e1 : P3 := mkP false true  false.
Definition e2 : P3 := mkP false false true.

(* lazy bit-flip diffusion (rational coefficients) *)
Definition step (f : RSigQ) : RSigQ :=
  fun x => (1 # 2) * f x + (1 # 6) * (f (xor3 x e0) + f (xor3 x e1) + f (xor3 x e2)).

(* its Walsh eigenvalue mu y = 1 - |y|/3 in {1, 2/3, 1/3, 0} *)
Definition mu (y : P3) : Q := (1 # 2) + (1 # 6) * (chrq e0 y + chrq e1 y + chrq e2 y).

Fixpoint iterate (k : nat) (f : RSigQ) : RSigQ :=
  match k with O => f | S k' => step (iterate k' f) end.

Fixpoint Qpow (q : Q) (k : nat) : Q :=
  match k with O => 1 | S k' => q * Qpow q k' end.

(* WHq is linear (symbolic scalar / sum -- no rational literal, so full  *)
(* cbn is safe here) *)
Lemma WHq_scale : forall a f y, WHq (fun x => a * f x) y == a * WHq f y.
Proof.
  intros a f [b0 b1 b2]; destruct b0, b1, b2;
    unfold WHq, chrq, dot, c0, c1, c2; cbn; ring.
Qed.

Lemma WHq_add : forall f g y, WHq (fun x => f x + g x) y == WHq f y + WHq g y.
Proof.
  intros f g [b0 b1 b2]; destruct b0, b1, b2;
    unfold WHq, chrq, dot, c0, c1, c2; cbn; ring.
Qed.

(* translation by a : F_2^3 becomes the character sign chrq a *)
Lemma WHq_shift : forall a f y, WHq (fun x => f (xor3 x a)) y == chrq a y * WHq f y.
Proof.
  intros [a0 a1 a2] f [y0 y1 y2]; destruct a0, a1, a2, y0, y1, y2;
    unfold WHq, chrq, dot, xor3, c0, c1, c2; cbn; ring.
Qed.

(* ----------------------------------------------------------------- *)
(* the diffusion is DIAGONALISED by Walsh                            *)
(* ----------------------------------------------------------------- *)

Theorem step_diagonal : forall f y, WHq (step f) y == mu y * WHq f y.
Proof.
  intros f y; unfold step, mu.
  rewrite (WHq_add (fun x => (1 # 2) * f x)
                   (fun x => (1 # 6) * (f (xor3 x e0) + f (xor3 x e1) + f (xor3 x e2)))).
  rewrite (WHq_scale (1 # 2) f).
  rewrite (WHq_scale (1 # 6)
             (fun x => f (xor3 x e0) + f (xor3 x e1) + f (xor3 x e2))).
  rewrite (WHq_add (fun x => f (xor3 x e0) + f (xor3 x e1))
                   (fun x => f (xor3 x e2))).
  rewrite (WHq_add (fun x => f (xor3 x e0)) (fun x => f (xor3 x e1))).
  rewrite (WHq_shift e0 f), (WHq_shift e1 f), (WHq_shift e2 f).
  ring.
Qed.

Theorem iterate_spectrum : forall k f y,
  WHq (iterate k f) y == Qpow (mu y) k * WHq f y.
Proof.
  induction k as [|k' IH]; intros f y.
  - cbn [iterate Qpow]; ring.
  - cbn [iterate Qpow]; rewrite step_diagonal, IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(* the spectrum: DC mode stationary, all others contract             *)
(* ----------------------------------------------------------------- *)

Theorem mu_zero : mu zero3 == 1.
Proof.
  unfold mu, chrq, dot, e0, e1, e2, zero3, c0, c1, c2; cbn; lra.
Qed.

Theorem mu_bound : forall y, y <> zero3 -> 0 <= mu y <= 2 # 3.
Proof.
  intros y Hy; destruct y as [b0 b1 b2]; destruct b0, b1, b2;
    try (exfalso; apply Hy; reflexivity);
    unfold mu, chrq, dot, e0, e1, e2, c0, c1, c2; cbn; lra.
Qed.

Lemma Qpow_one_base : forall a k, a == 1 -> Qpow a k == 1.
Proof.
  intros a k Ha; induction k as [|k' IH]; simpl;
    [ reflexivity | rewrite IH, Qmult_1_r; exact Ha ].
Qed.

(* the DC coefficient (total heat / spatial mean) is conserved *)
Theorem dc_preserved : forall k f, WHq (iterate k f) zero3 == WHq f zero3.
Proof.
  intros k f; rewrite iterate_spectrum.
  assert (H : Qpow (mu zero3) k == 1) by (apply Qpow_one_base; exact mu_zero).
  rewrite H; ring.
Qed.

(* (The k-fold geometric decay bound |WHq (iterate k f) y| <= (2/3)^k   *)
(*  |WHq f y| holds by mu_bound + iterate_spectrum; over Q it needs a   *)
(*  Qabs/Qpow monotonicity layer and is omitted here -- the eigenvalue  *)
(*  bounds above already give: DC stationary, every other mode <= 2/3.) *)

Theorem heatflowQ :
  (forall f y, WHq (step f) y == mu y * WHq f y)
  /\ (forall k f y, WHq (iterate k f) y == Qpow (mu y) k * WHq f y)
  /\ mu zero3 == 1
  /\ (forall y, y <> zero3 -> 0 <= mu y <= 2 # 3)
  /\ (forall k f, WHq (iterate k f) zero3 == WHq f zero3).
Proof.
  split; [ exact step_diagonal | ].
  split; [ exact iterate_spectrum | ].
  split; [ exact mu_zero | ].
  split; [ exact mu_bound | exact dc_preserved ].
Qed.

Print Assumptions heatflowQ.
