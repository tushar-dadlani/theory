(* ================================================================= *)
(*  IntPoly.v                                                        *)
(*                                                                    *)
(*  A minimal integer-polynomial layer ℤ[X], as the foundation for   *)
(*  the cyclotomic polynomials Φ_n and the product identity          *)
(*  ∏_{d|n} Φ_d(X) = X^n − 1 (needed for "infinitely many primes     *)
(*  ≡ 1 (mod n)").                                                    *)
(*                                                                    *)
(*  Polynomials are lists of Z coefficients, low degree first        *)
(*  ([c0; c1; c2] = c0 + c1 X + c2 X²).  Trailing zeros are allowed  *)
(*  (no canonical form); semantic equality is agreement of eval at   *)
(*  every point, which is all the downstream development needs.       *)
(*                                                                    *)
(*  Delivered here: the ring operations (padd, pscale, pmul, pmonom) *)
(*  with the EVALUATION HOMOMORPHISM (eval commutes with +, *, scale,*)
(*  monomials), and the geometric divisibility X^m−1 | X^n−1 for      *)
(*  m|n, with an EXPLICIT integer cofactor.  AXIOM-FREE.             *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition poly := list Z.

(* Horner evaluation:  eval [c0;c1;c2] x = c0 + x*(c1 + x*(c2 + x*0)) *)
Fixpoint eval (p : poly) (x : Z) : Z :=
  match p with
  | [] => 0
  | c :: p' => c + x * eval p' x
  end.

(* ----------------------------------------------------------------- *)
(*  Addition                                                         *)
(* ----------------------------------------------------------------- *)
Fixpoint padd (p q : poly) : poly :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => (a + b) :: padd p' q'
  end.

Lemma eval_add : forall p q x, eval (padd p q) x = eval p x + eval q x.
Proof.
  induction p as [|a p IH]; intros [|b q] x; simpl; try ring.
  rewrite IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Scaling by a constant                                            *)
(* ----------------------------------------------------------------- *)
Definition pscale (c : Z) (p : poly) : poly := map (Z.mul c) p.

Lemma eval_scale : forall c p x, eval (pscale c p) x = c * eval p x.
Proof.
  intros c p x; induction p as [|a p IH]; simpl; [ ring | ].
  change (map (Z.mul c) p) with (pscale c p); rewrite IH; ring.
Qed.

(* multiply by X : prepend a zero coefficient *)
Lemma eval_shift : forall p x, eval (0 :: p) x = x * eval p x.
Proof. intros; simpl; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  Multiplication                                                   *)
(* ----------------------------------------------------------------- *)
Fixpoint pmul (p q : poly) : poly :=
  match p with
  | [] => []
  | a :: p' => padd (pscale a q) (0 :: pmul p' q)
  end.

Lemma eval_mul : forall p q x, eval (pmul p q) x = eval p x * eval q x.
Proof.
  induction p as [|a p IH]; intros q x; simpl; [ ring | ].
  rewrite eval_add, eval_scale, eval_shift, IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Constants, X, and monomials X^n                                  *)
(* ----------------------------------------------------------------- *)
Definition pconst (c : Z) : poly := [c].
Lemma eval_const : forall c x, eval (pconst c) x = c.
Proof. intros; simpl; ring. Qed.

(* X^n = 0 :: 0 :: ... :: 0 :: [1]  (n zeros then 1) *)
Fixpoint pmonom (n : nat) : poly :=
  match n with
  | O => [1]
  | S k => 0 :: pmonom k
  end.

Lemma eval_monom : forall n x, eval (pmonom n) x = x ^ Z.of_nat n.
Proof.
  induction n as [|n IH]; intro x.
  - cbn [pmonom eval Z.of_nat]; rewrite Z.pow_0_r; ring.
  - cbn [pmonom eval]; rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  X^n − 1                                                          *)
(* ----------------------------------------------------------------- *)
Definition Xn1 (n : nat) : poly := padd (pmonom n) (pconst (-1)).

Lemma eval_Xn1 : forall n x, eval (Xn1 n) x = x ^ Z.of_nat n - 1.
Proof.
  intros; unfold Xn1; rewrite eval_add, eval_monom, eval_const; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Polynomial divisibility (semantic: agreement of eval everywhere) *)
(* ----------------------------------------------------------------- *)
Definition pdivides (p q : poly) : Prop :=
  exists r : poly, forall x, eval q x = eval p x * eval r x.

Lemma pdivides_refl : forall p, pdivides p p.
Proof. intro p; exists (pconst 1); intro x; rewrite eval_const; ring. Qed.

Lemma pdivides_trans : forall p q r, pdivides p q -> pdivides q r -> pdivides p r.
Proof.
  intros p q r [s Hs] [t Ht]; exists (pmul s t); intro x.
  rewrite Ht, Hs, eval_mul; ring.
Qed.

(* the geometric cofactor  1 + X^m + X^{2m} + ... + X^{(k-1)m}       *)
Fixpoint geo (m k : nat) : poly :=
  match k with
  | O => []
  | S j => padd (pmonom (m * j)) (geo m j)
  end.

(* the telescoping identity:  (X^m − 1) · geo m k = X^{m k} − 1       *)
Lemma geo_telescope : forall m k x,
  (x ^ Z.of_nat m - 1) * eval (geo m k) x = x ^ Z.of_nat (m * k) - 1.
Proof.
  intros m k x; induction k as [|k IH]; simpl.
  - rewrite Nat.mul_0_r; simpl; ring.
  - rewrite eval_add, eval_monom.
    replace (m * S k)%nat with (m * k + m)%nat by lia.
    rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    (* (x^m−1)(x^{m k} + geo) = x^{m k+m} − 1 *)
    rewrite Z.mul_add_distr_l, IH.
    ring.
Qed.

(* X^m − 1  divides  X^n − 1  whenever m | n, with explicit cofactor *)
Theorem Xn1_dvd : forall m n, Nat.divide m n -> pdivides (Xn1 m) (Xn1 n).
Proof.
  intros m n [k Hk]; subst n; exists (geo m k); intro x.
  rewrite !eval_Xn1, geo_telescope, (Nat.mul_comm m k); ring.
Qed.

(* the corresponding INTEGER divisibility (evaluate at a) *)
Corollary Xn1_dvd_val : forall m n a, Nat.divide m n ->
  (a ^ Z.of_nat m - 1 | a ^ Z.of_nat n - 1).
Proof.
  intros m n a Hmn; destruct (Xn1_dvd m n Hmn) as [r Hr].
  exists (eval r a); pose proof (Hr a) as H; rewrite !eval_Xn1 in H; lia.
Qed.

Print Assumptions Xn1_dvd.
Print Assumptions Xn1_dvd_val.

(* ================================================================= *)
(*  END IntPoly.v                                                    *)
(*  Integer polynomials ℤ[X] with the evaluation homomorphism, and   *)
(*  the geometric divisibility X^m−1 | X^n−1 (m|n) with an explicit   *)
(*  cofactor.  Foundation for the cyclotomic Φ_n.  Closed under the   *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
