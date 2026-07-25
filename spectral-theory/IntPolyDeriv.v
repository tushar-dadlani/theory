(* ================================================================= *)
(*  IntPolyDeriv.v                                                   *)
(*                                                                    *)
(*  THE FORMAL DERIVATIVE in ℤ[X] (brick toward general-n Dirichlet).*)
(*                                                                    *)
(*  Delivers the product rule (p·q)′ = p′·q + p·q′ (at eval level)   *)
(*  and (X^n−1)′ = n·X^{n−1}.  Used in the prime-divisor lemma: a     *)
(*  prime q dividing two distinct cyclotomic factors Φ_e(a), Φ_n(a)   *)
(*  makes a a double root of X^n−1 mod q, so q ∣ (X^n−1)′(a) =        *)
(*  n·a^{n−1}, forcing q ∣ n.  AXIOM-FREE.                           *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia Arith.
Import ListNotations.
Require Import IntPoly.
Open Scope Z_scope.

Fixpoint pderiv_aux (p : poly) (k : nat) : poly :=
  match p with
  | [] => []
  | c :: p' => (Z.of_nat k * c) :: pderiv_aux p' (S k)
  end.

Definition pderiv (p : poly) : poly :=
  match p with [] => [] | _ :: p' => pderiv_aux p' 1 end.

Lemma zofnat_S : forall k, Z.of_nat (S k) = Z.of_nat k + 1.
Proof. intro k; rewrite Nat2Z.inj_succ; lia. Qed.

Lemma pderiv_aux_shift : forall p k x,
  eval (pderiv_aux p (S k)) x = eval (pderiv_aux p k) x + eval p x.
Proof.
  induction p as [|c p' IH]; intros k x; [ simpl; ring | ].
  cbn [pderiv_aux eval]; rewrite zofnat_S, (IH (S k) x); ring.
Qed.

Lemma pderiv_aux_add : forall p q k x,
  eval (pderiv_aux (padd p q) k) x = eval (pderiv_aux p k) x + eval (pderiv_aux q k) x.
Proof.
  induction p as [|a p IH]; intros [|b q] k x; simpl; try ring.
  cbn [pderiv_aux eval]; rewrite (IH q (S k) x); ring.
Qed.

Lemma pderiv_aux_scale : forall c p k x,
  eval (pderiv_aux (pscale c p) k) x = c * eval (pderiv_aux p k) x.
Proof.
  intros c p k x; revert k; induction p as [|a p IH]; intro k; [ simpl; ring | ].
  cbn [pscale map pderiv_aux eval]; change (map (Z.mul c) p) with (pscale c p).
  rewrite (IH (S k)); ring.
Qed.

Lemma pderiv_cons_eval : forall c p' x,
  eval (pderiv (c :: p')) x = eval p' x + x * eval (pderiv p') x.
Proof.
  intros c p' x; destruct p' as [|d p'']; [ simpl; ring | ].
  cbn [pderiv pderiv_aux eval]; change (Z.of_nat 1) with 1%Z.
  rewrite (pderiv_aux_shift p'' 1 x); ring.
Qed.

Lemma pderiv_add_eval : forall p q x,
  eval (pderiv (padd p q)) x = eval (pderiv p) x + eval (pderiv q) x.
Proof.
  intros [|a p] [|b q] x; try (simpl; ring).
  cbn [padd pderiv]; apply (pderiv_aux_add p q 1 x).
Qed.

Lemma pderiv_scale_eval : forall c p x,
  eval (pderiv (pscale c p)) x = c * eval (pderiv p) x.
Proof.
  intros c [|a p] x; [ simpl; ring | ].
  cbn [pscale map pderiv]; change (map (Z.mul c) p) with (pscale c p).
  apply (pderiv_aux_scale c p 1 x).
Qed.

Theorem pderiv_mul_eval : forall p q x,
  eval (pderiv (pmul p q)) x = eval (pderiv p) x * eval q x + eval p x * eval (pderiv q) x.
Proof.
  induction p as [|c p' IH]; intros q x; [ simpl; ring | ].
  cbn [pmul]; rewrite pderiv_add_eval, pderiv_scale_eval.
  rewrite (pderiv_cons_eval 0 (pmul p' q) x), eval_mul, (IH q x).
  rewrite (pderiv_cons_eval c p' x).
  change (eval (c :: p') x) with (c + x * eval p' x); ring.
Qed.

Lemma peval_pderiv_pmonom : forall n x,
  eval (pderiv (pmonom n)) x = Z.of_nat n * x ^ Z.of_nat (Nat.pred n).
Proof.
  induction n as [|n IH]; intro x.
  - simpl; change (Z.of_nat 0) with 0%Z; rewrite ?Z.pow_0_r; ring.
  - cbn [pmonom]; rewrite (pderiv_cons_eval 0 (pmonom n) x), eval_monom, IH, zofnat_S.
    destruct n as [|n'].
    + change (Z.of_nat 0) with 0%Z; rewrite ?Z.pow_0_r; ring.
    + cbn [Nat.pred]; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring.
Qed.

Theorem peval_pderiv_Xn1 : forall n x,
  eval (pderiv (Xn1 n)) x = Z.of_nat n * x ^ Z.of_nat (Nat.pred n).
Proof.
  intros n x; unfold Xn1; rewrite pderiv_add_eval, peval_pderiv_pmonom.
  unfold pconst; cbn [pderiv]; simpl; ring.
Qed.

Print Assumptions pderiv_mul_eval.
Print Assumptions peval_pderiv_Xn1.

(* ================================================================= *)
(*  END IntPolyDeriv.v                                               *)
(*  Formal derivative in ℤ[X]: product rule and (X^n−1)′ = n·X^{n−1}. *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
