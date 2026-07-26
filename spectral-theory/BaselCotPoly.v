(* ================================================================= *)
(*  BaselCotPoly.v  —  toward sin((2m+1)θ) as a polynomial in cot²θ.  *)
(*                                                                    *)
(*  Part 1 (this commit): the BINOMIAL THEOREM over the complex ring  *)
(*  `Cbinomial : (x+y)^n = Σ_i C(n,i)·xⁱ·y^(n−i)` (over ComplexField),*)
(*  plus the `Csum` toolkit it needs.  This is the algebraic engine   *)
(*  for extracting the odd-multiple-angle expansion of sin.           *)
(*                                                                    *)
(*  Over the classical `Reals` (quarantined).                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Binomial Arith.
Require Import ComplexField RootsOfUnity.
Local Open Scope R_scope.

Lemma Csum_add : forall f g N, Csum (fun i => Cadd (f i) (g i)) N = Cadd (Csum f N) (Csum g N).
Proof. intros f g N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite IH; ring ]. Qed.
Lemma Csum_mul_l : forall c f N, Csum (fun i => Cmul c (f i)) N = Cmul c (Csum f N).
Proof. intros c f N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite IH; ring ]. Qed.
Lemma Csum_ext_lt : forall f g N, (forall k, (k < N)%nat -> f k = g k) -> Csum f N = Csum g N.
Proof. intros f g N; induction N as [|N IH]; intro H; cbn [Csum]; [ reflexivity | ].
  rewrite IH by (intros k Hk; apply H; lia); rewrite (H N) by lia; reflexivity. Qed.
Lemma Csum_decomp : forall f N, Csum f (S N) = Cadd (f O) (Csum (fun i => f (S i)) N).
Proof. intros f N; induction N as [|N IH].
  - cbn [Csum]; ring.
  - change (Csum f (S (S N))) with (Cadd (Csum f (S N)) (f (S N))); rewrite IH.
    change (Csum (fun i => f (S i)) (S N)) with (Cadd (Csum (fun i => f (S i)) N) (f (S N))); ring.
Qed.
Lemma RtoC_add : forall a b, RtoC (a + b) = Cadd (RtoC a) (RtoC b).
Proof. intros a b; unfold RtoC, Cadd; cbn; f_equal; ring. Qed.
Lemma C_n_0 : forall n, Binomial.C n 0 = 1.
Proof. intro n; unfold Binomial.C; rewrite Nat.sub_0_r; simpl (fact 0); simpl (INR 1); field; apply INR_fact_neq_0. Qed.
Lemma C_n_n : forall n, Binomial.C n n = 1.
Proof. intro n; unfold Binomial.C; rewrite Nat.sub_diag; simpl (fact 0); simpl (INR 1); field; apply INR_fact_neq_0. Qed.
Definition bterm (x y : C) (n i : nat) : C :=
  Cmul (RtoC (Binomial.C n i)) (Cmul (Cpow x i) (Cpow y (n - i))).
Lemma bterm_pascal : forall x y n i, (i < n)%nat ->
  bterm x y (S n) (S i) = Cadd (Cmul x (bterm x y n i)) (Cmul y (bterm x y n (S i))).
Proof.
  intros x y n i Hi; unfold bterm.
  rewrite <- pascal by exact Hi; rewrite RtoC_add.
  replace (S n - S i)%nat with (n - i)%nat by lia.
  replace (n - i)%nat with (S (n - S i))%nat by lia.
  cbn [Cpow]; ring.
Qed.
Lemma Cbinomial : forall (x y : C) n, Cpow (Cadd x y) n = Csum (bterm x y n) (S n).
Proof.
  intros x y n; induction n as [|n IH].
  - cbn [Cpow Csum]; unfold bterm; cbn [Cpow Nat.sub].
    replace (Binomial.C 0 0) with 1 by (unfold Binomial.C; cbn; field); replace (RtoC 1) with C1 by reflexivity; ring.
  - cbn [Cpow]; rewrite IH.
    replace (Cmul (Cadd x y) (Csum (bterm x y n) (S n)))
      with (Cadd (Csum (fun i => Cmul x (bterm x y n i)) (S n))
                 (Csum (fun i => Cmul y (bterm x y n i)) (S n)))
      by (rewrite <- !Csum_mul_l, <- Csum_add; apply Csum_ext; intro k; ring).
    change (Csum (bterm x y (S n)) (S (S n)))
      with (Cadd (Csum (bterm x y (S n)) (S n)) (bterm x y (S n) (S n))).
    rewrite (Csum_decomp (bterm x y (S n)) n).
    replace (bterm x y (S n) O) with (Cmul y (bterm x y n O)).
    2:{ unfold bterm; rewrite !C_n_0; replace (S n - 0)%nat with (S (n - 0)) by lia;
        cbn [Cpow]; replace (RtoC 1) with C1 by reflexivity; ring. }
    replace (bterm x y (S n) (S n)) with (Cmul x (bterm x y n n)).
    2:{ unfold bterm; rewrite !C_n_n, !Nat.sub_diag; cbn [Cpow];
        replace (RtoC 1) with C1 by reflexivity; ring. }
    rewrite (Csum_ext_lt (fun i => bterm x y (S n) (S i))
                      (fun i => Cadd (Cmul x (bterm x y n i)) (Cmul y (bterm x y n (S i)))) n)
      by (intros k Hk; apply bterm_pascal; exact Hk).
    rewrite Csum_add.
    rewrite (Csum_decomp (fun i => Cmul y (bterm x y n i)) n).
    change (Csum (fun i => Cmul x (bterm x y n i)) (S n))
      with (Cadd (Csum (fun i => Cmul x (bterm x y n i)) n) (Cmul x (bterm x y n n))).
    ring.
Qed.

(* ================================================================= *)
(*  END BaselCotPoly.v (Part 1: complex binomial theorem).           *)
(* ================================================================= *)
