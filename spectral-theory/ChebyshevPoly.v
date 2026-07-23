(* ================================================================= *)
(*  ChebyshevPoly.v                                                  *)
(*                                                                    *)
(*  CHEBYSHEV POLYNOMIALS of the first kind, T_n, straight from       *)
(*  de Moivre (EulerFormula):  T_n(cos t) = cos(n t).                *)
(*                                                                    *)
(*  (Distinct from Chebyshev.v, which is the number-theoretic         *)
(*   Chebyshev function psi(N) = sum Lam(d) floor(N/d).)             *)
(*                                                                    *)
(*  Defined by the recurrence                                        *)
(*     T_0 = 1,  T_1 = x,  T_{n+2} = 2 x T_{n+1} - T_n,               *)
(*  we prove the defining trigonometric identity                     *)
(*     Tcheb n (cos t) = cos (n t)                                   *)
(*  -- the polynomial recurrence mirrors the cosine recurrence        *)
(*     cos((n+2)t) = 2 cos t cos((n+1)t) - cos(n t)                  *)
(*  which is itself the real part of de Moivre, (Cexp t)^n =          *)
(*  Cexp(n t) (Tcheb_Re: T_n(cos t) = Re((Cexp t)^n)).               *)
(*                                                                    *)
(*  Consequences: T_n(1) = 1, and the n roots of T_n at              *)
(*  cos((2k+1) pi / 2n)  (Tcheb_root).                               *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via cos/sin).       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField RootsOfUnity EulerFormula.
Open Scope R_scope.

Fixpoint Tcheb (n : nat) (x : R) : R :=
  match n with
  | O => 1
  | S O => x
  | S (S k as m) => 2 * x * Tcheb m x - Tcheb k x
  end.

Lemma Tcheb_rec : forall n x, Tcheb (S (S n)) x = 2 * x * Tcheb (S n) x - Tcheb n x.
Proof. reflexivity. Qed.

(* concrete low-order polynomials *)
Lemma Tcheb_2 : forall x, Tcheb 2 x = 2 * x * x - 1.       Proof. intro x; simpl; ring. Qed.
Lemma Tcheb_3 : forall x, Tcheb 3 x = 4 * (x * x * x) - 3 * x.  Proof. intro x; simpl; ring. Qed.

(* the cosine recurrence: cos((n+2)t) = 2 cos t cos((n+1)t) - cos(n t) *)
Lemma cos_rec : forall n t,
  cos (INR (S (S n)) * t) = 2 * cos t * cos (INR (S n) * t) - cos (INR n * t).
Proof.
  intros n t.
  replace (INR (S (S n)) * t) with (INR (S n) * t + t) by (rewrite !S_INR; ring).
  replace (INR n * t) with (INR (S n) * t - t) by (rewrite S_INR; ring).
  rewrite cos_plus, cos_minus; ring.
Qed.

(* THE defining identity: T_n(cos t) = cos(n t) *)
Theorem Tcheb_cos : forall n t, Tcheb n (cos t) = cos (INR n * t).
Proof.
  assert (H : forall n, (forall t, Tcheb n (cos t) = cos (INR n * t))
                     /\ (forall t, Tcheb (S n) (cos t) = cos (INR (S n) * t))).
  { induction n as [|n [IH0 IH1]].
    - split; intro t.
      + replace (INR 0 * t) with 0 by (simpl INR; ring); rewrite cos_0; reflexivity.
      + replace (INR 1 * t) with t by (simpl INR; ring); reflexivity.
    - split; [ exact IH1 | intro t ].
      rewrite Tcheb_rec, (IH1 t), (IH0 t), <- cos_rec; reflexivity. }
  intros n t; apply (proj1 (H n) t).
Qed.

(* de Moivre link: T_n(cos t) is the real part of (Cexp t)^n *)
Lemma Tcheb_Re : forall n t, Tcheb n (cos t) = Re (Cpow (Cexp t) n).
Proof. intros n t; rewrite Tcheb_cos, Cpow_Cexp; unfold Cexp; reflexivity. Qed.

(* boundary value T_n(1) = 1 *)
Corollary Tcheb_at_1 : forall n, Tcheb n 1 = 1.
Proof. intro n; pose proof (Tcheb_cos n 0) as H; rewrite Rmult_0_r, cos_0 in H; exact H. Qed.

(* T_n(-1) = cos(n pi) *)
Corollary Tcheb_at_m1 : forall n, Tcheb n (-1) = cos (INR n * PI).
Proof. intro n; pose proof (Tcheb_cos n PI) as H; rewrite cos_PI in H; exact H. Qed.

(* cos of an odd multiple of pi/2 is zero *)
Lemma cos_odd_pihalf : forall k, cos ((2 * INR k + 1) * (PI / 2)) = 0.
Proof.
  induction k as [|k IH].
  - replace ((2 * INR 0 + 1) * (PI / 2)) with (PI / 2) by (simpl INR; field); apply cos_PI2.
  - replace ((2 * INR (S k) + 1) * (PI / 2)) with ((2 * INR k + 1) * (PI / 2) + PI)
      by (rewrite S_INR; field).
    rewrite cos_plus, cos_PI, sin_PI, IH; ring.
Qed.

(* the n roots of T_n:  cos((2k+1) pi / 2n) *)
Corollary Tcheb_root : forall n k, (1 <= n)%nat ->
  Tcheb n (cos ((2 * INR k + 1) * (PI / (2 * INR n)))) = 0.
Proof.
  intros n k Hn; rewrite Tcheb_cos.
  assert (Hn0 : INR n <> 0) by (apply not_0_INR; lia).
  replace (INR n * ((2 * INR k + 1) * (PI / (2 * INR n)))) with ((2 * INR k + 1) * (PI / 2))
    by (field; exact Hn0).
  apply cos_odd_pihalf.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER                                                           *)
(* ----------------------------------------------------------------- *)

Theorem chebyshev_poly :
     (forall n x, Tcheb (S (S n)) x = 2 * x * Tcheb (S n) x - Tcheb n x)
  /\ (forall n t, Tcheb n (cos t) = cos (INR n * t))
  /\ (forall n t, Tcheb n (cos t) = Re (Cpow (Cexp t) n))
  /\ (forall n, Tcheb n 1 = 1)
  /\ (forall n k, (1 <= n)%nat ->
        Tcheb n (cos ((2 * INR k + 1) * (PI / (2 * INR n)))) = 0).
Proof.
  split; [ exact Tcheb_rec | ].
  split; [ exact Tcheb_cos | ].
  split; [ exact Tcheb_Re | ].
  split; [ exact Tcheb_at_1 | exact Tcheb_root ].
Qed.

Print Assumptions chebyshev_poly.

(* ================================================================= *)
(*  END ChebyshevPoly.v                                              *)
(*  Chebyshev polynomials T_n via the recurrence, with T_n(cos t) =   *)
(*  cos(n t) (the real part of de Moivre, (Cexp t)^n = Cexp(n t)),    *)
(*  T_n(1)=1, and the roots at cos((2k+1)pi/2n).  Classical Reals      *)
(*  axioms (quarantined, via cos/sin).                                *)
(* ================================================================= *)
