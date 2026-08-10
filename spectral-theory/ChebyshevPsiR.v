(* ================================================================= *)
(*  ChebyshevPsiR.v  —  Newman A3: the real-argument Chebyshev psi.       *)
(*                                                                    *)
(*  psiR x = psi (floor x) = sum_{n <= x} Lam(n)  for real x >= 0,        *)
(*  the step function that Newman's integrand ψ(e^t)e^{-t}-1 is built     *)
(*  from.  Key facts:                                                   *)
(*    psiR_step   : psiR is constant = psi N on [N, N+1),                *)
(*    psiR_nonneg : 0 <= psiR x,                                        *)
(*    psiR_mono   : nondecreasing,                                      *)
(*    psiR_upper  : psiR x <= x * Kup   (the linear Chebyshev bound).    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import Chebyshev ChebyshevBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the nat floor of a nonnegative real                                *)
(* ----------------------------------------------------------------- *)

Definition floorN (x : R) : nat := Z.to_nat (Int_part x).

Lemma Int_part_nonneg : forall x, 0 <= x -> (0 <= Int_part x)%Z.
Proof.
  intros x Hx; destruct (base_Int_part x) as [_ H2].
  assert (Hlt : (-1 < IZR (Int_part x))%R) by lra.
  replace (-1)%R with (IZR (-1)) in Hlt by (simpl; ring).
  apply lt_IZR in Hlt; lia.
Qed.

Lemma INR_floorN : forall x, 0 <= x -> INR (floorN x) = IZR (Int_part x).
Proof.
  intros x Hx; unfold floorN; rewrite INR_IZR_INZ, Z2Nat.id
    by (apply Int_part_nonneg; exact Hx); reflexivity.
Qed.

Lemma floorN_spec : forall x, 0 <= x -> INR (floorN x) <= x /\ x < INR (floorN x) + 1.
Proof.
  intros x Hx; rewrite (INR_floorN x Hx); destruct (base_Int_part x) as [H1 H2]; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the real-argument Chebyshev psi                                    *)
(* ----------------------------------------------------------------- *)

Definition psiR (x : R) : R := psi (floorN x).

Lemma psiR_nonneg : forall x, 0 <= psiR x.
Proof. intro x; unfold psiR; rewrite <- psi_0; apply psi_mono; lia. Qed.

(*  psiR is constant = psi N on [N, N+1)  *)
Lemma psiR_step : forall (N : nat) x, INR N <= x < INR (S N) -> psiR x = psi N.
Proof.
  intros N x [Hlo Hhi]; unfold psiR; f_equal.
  assert (Hx0 : 0 <= x) by (apply Rle_trans with (INR N); [ apply pos_INR | exact Hlo ]).
  destruct (floorN_spec x Hx0) as [Hf1 Hf2]; rewrite S_INR in Hhi.
  assert (H1 : (N < S (floorN x))%nat) by (apply INR_lt; rewrite S_INR; lra).
  assert (H2 : (floorN x < S N)%nat) by (apply INR_lt; rewrite S_INR; lra).
  lia.
Qed.

Lemma psiR_mono : forall x y, 0 <= x -> x <= y -> psiR x <= psiR y.
Proof.
  intros x y Hx Hxy; unfold psiR; apply psi_mono.
  destruct (floorN_spec x Hx) as [Hf1 _].
  assert (Hy : 0 <= y) by lra; destruct (floorN_spec y Hy) as [_ Hg2].
  assert (floorN x < S (floorN y))%nat by (apply INR_lt; rewrite S_INR; lra); lia.
Qed.

Lemma Kup_pos : 0 < Kup.
Proof.
  unfold Kup; assert (0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra); lra.
Qed.

(*  the linear Chebyshev bound in real argument  *)
Lemma psiR_upper : forall x, 0 <= x -> psiR x <= x * Kup.
Proof.
  intros x Hx; unfold psiR; eapply Rle_trans; [ apply psi_upper | ].
  apply Rmult_le_compat_r; [ left; apply Kup_pos | ].
  destruct (floorN_spec x Hx) as [Hf1 _]; exact Hf1.
Qed.

Lemma psiR_0 : psiR 0 = 0.
Proof.
  assert (Hip : Int_part 0 = 0%Z).
  { assert (H0 : (0 <= Int_part 0)%Z) by (apply Int_part_nonneg; lra).
    destruct (base_Int_part 0) as [H1 _].
    assert (Hle : (Int_part 0 <= 0)%Z) by (apply le_IZR; simpl; lra).
    lia. }
  unfold psiR, floorN; rewrite Hip; simpl; apply psi_0.
Qed.

Print Assumptions psiR_upper.

(* ================================================================= *)
(*  END ChebyshevPsiR.v — the real-argument Chebyshev psi step function.  *)
(*  Next: the piecewise-continuous Laplace transform (psiR e^t is a       *)
(*  step function; its transform is well-defined via Riemann             *)
(*  integrability of step x continuous on each [0,T]).                    *)
(* ================================================================= *)
