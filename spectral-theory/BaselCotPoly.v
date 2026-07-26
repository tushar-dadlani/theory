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
(*  Part 2: extraction — sin((2m+1)θ) as a polynomial in cot²θ.       *)
(* ================================================================= *)
Definition Rcot (x : R) : R := cos x / sin x.

Lemma RtoC_mul : forall a b, RtoC (a * b) = Cmul (RtoC a) (RtoC b).
Proof. intros a b; unfold RtoC, Cmul; cbn; f_equal; ring. Qed.
Lemma Cpow_Cmul : forall a b n, Cpow (Cmul a b) n = Cmul (Cpow a n) (Cpow b n).
Proof. intros a b n; induction n as [|n IH]; cbn [Cpow]; [ ring | rewrite IH; ring ]. Qed.
Lemma Cpow_RtoC : forall r n, Cpow (RtoC r) n = RtoC (r ^ n).
Proof. intros r n; induction n as [|n IH]; cbn [Cpow pow]; [ reflexivity | rewrite IH, RtoC_mul; reflexivity ]. Qed.
Lemma Im_Cadd : forall a b, Im (Cadd a b) = (Im a + Im b)%R.
Proof. intros a b; unfold Cadd; reflexivity. Qed.
Lemma Im_Copp : forall a, Im (Copp a) = (- Im a)%R.
Proof. intro a; unfold Copp; reflexivity. Qed.
Lemma Im_Cmul_RtoC : forall z r, Im (Cmul z (RtoC r)) = (Im z * r)%R.
Proof. intros z r; unfold Cmul, RtoC; cbn; ring. Qed.

Fixpoint RSm (g : nat -> R) (N : nat) : R := match N with O => 0%R | S k => (RSm g k + g k)%R end.
Lemma Im_Csum : forall f N, Im (Csum f N) = RSm (fun i => Im (f i)) N.
Proof. intros f N; induction N as [|N IH]; cbn [Csum RSm]; [ reflexivity | rewrite Im_Cadd, IH; reflexivity ]. Qed.

Lemma Cpow_Ci_SS : forall i, Cpow Ci (S (S i)) = Copp (Cpow Ci i).
Proof.
  intro i; replace (Cpow Ci (S (S i))) with (Cmul (Cmul Ci Ci) (Cpow Ci i)) by (cbn [Cpow]; ring).
  rewrite Ci_sq; ring.
Qed.
Lemma Im_Cpow_Ci_even : forall j, Im (Cpow Ci (2 * j)) = 0%R.
Proof.
  induction j as [|j IH]; [ reflexivity | ].
  replace (2 * S j)%nat with (S (S (2 * j))) by lia.
  rewrite Cpow_Ci_SS, Im_Copp, IH; ring.
Qed.
Lemma Im_Cpow_Ci_odd : forall j, Im (Cpow Ci (2 * j + 1)) = ((-1) ^ j)%R.
Proof.
  induction j as [|j IH].
  - replace (2 * 0 + 1)%nat with 1%nat by lia; cbn [Cpow pow]; unfold Cmul, Ci, C1; cbn; ring.
  - replace (2 * S j + 1)%nat with (S (S (2 * j + 1))) by lia.
    rewrite Cpow_Ci_SS, Im_Copp, IH; cbn [pow]; ring.
Qed.

Lemma RSm_pair : forall g m, RSm g (2 * S m) = sum_f_R0 (fun j => (g (2 * j)%nat + g (2 * j + 1)%nat)%R) m.
Proof.
  intros g m; induction m as [|m IH].
  - cbn; ring.
  - replace (2 * S (S m))%nat with (S (S (2 * S m))) by lia; cbn [RSm]; rewrite IH.
    rewrite (tech5 (fun j => (g (2 * j)%nat + g (2 * j + 1)%nat)%R) m).
    replace (S (2 * S m)) with (2 * S m + 1)%nat by lia; ring.
Qed.

Definition cx (θ : R) : C := Cmul Ci (RtoC (sin θ)).
Definition cy (θ : R) : C := RtoC (cos θ).

Lemma bterm_Im : forall m θ i,
  Im (bterm (cx θ) (cy θ) (2 * m + 1) i)
  = (Im (Cpow Ci i) * (Binomial.C (2 * m + 1) i * sin θ ^ i * cos θ ^ (2 * m + 1 - i)))%R.
Proof.
  intros m θ i; unfold bterm, cx, cy.
  assert (Hb : Cmul (RtoC (Binomial.C (2*m+1) i)) (Cmul (Cpow (Cmul Ci (RtoC (sin θ))) i) (Cpow (RtoC (cos θ)) (2*m+1-i)))
             = Cmul (Cpow Ci i) (RtoC (Binomial.C (2*m+1) i * sin θ ^ i * cos θ ^ (2*m+1-i)))).
  { rewrite Cpow_Cmul, !Cpow_RtoC, !RtoC_mul; ring. }
  rewrite Hb, Im_Cmul_RtoC; reflexivity.
Qed.

Lemma sin_odd_expand : forall m θ,
  sin (INR (2 * m + 1) * θ) =
  sum_f_R0 (fun j => (-1) ^ j * Binomial.C (2 * m + 1) (2 * j + 1)
                     * cos θ ^ (2 * (m - j)) * sin θ ^ (2 * j + 1)) m.
Proof.
  intros m θ.
  assert (Hxy : Cadd (cx θ) (cy θ) = {| Re := cos θ; Im := sin θ |})
    by (unfold cx, cy, Ci, RtoC, Cmul, Cadd; cbn; f_equal; ring).
  assert (Hsin : sin (INR (2 * m + 1) * θ) = Im (Csum (bterm (cx θ) (cy θ) (2 * m + 1)) (S (2 * m + 1)))).
  { rewrite <- Cbinomial, Hxy, de_moivre; reflexivity. }
  rewrite Hsin, Im_Csum.
  replace (S (2 * m + 1)) with (2 * S m)%nat by lia.
  rewrite RSm_pair; apply sum_eq; intros j Hj.
  rewrite (bterm_Im m θ (2 * j)), (bterm_Im m θ (2 * j + 1)).
  rewrite Im_Cpow_Ci_even, Im_Cpow_Ci_odd.
  replace (2 * m + 1 - (2 * j + 1))%nat with (2 * (m - j))%nat by lia.
  ring.
Qed.

Definition Pcot (m : nat) (x : R) : R :=
  sum_f_R0 (fun j => (-1) ^ j * Binomial.C (2 * m + 1) (2 * j + 1) * x ^ (m - j)) m.

Lemma sin_eq_sinpow_Pcot : forall m θ, sin θ <> 0 ->
  sin (INR (2 * m + 1) * θ) = sin θ ^ (2 * m + 1) * Pcot m (Rcot θ ^ 2).
Proof.
  intros m θ Hs; rewrite sin_odd_expand; unfold Pcot; rewrite scal_sum.
  apply sum_eq; intros j Hj; unfold Rcot.
  replace (sin θ ^ (2 * m + 1)) with (sin θ ^ (2 * (m - j)) * sin θ ^ (2 * j + 1))
    by (rewrite <- pow_add; f_equal; lia).
  rewrite <- (pow_mult (cos θ / sin θ) 2 (m - j)).
  assert (Hcs : (cos θ / sin θ) * sin θ = cos θ) by (field; exact Hs).
  assert (Hk : cos θ ^ (2 * (m - j)) = (cos θ / sin θ) ^ (2 * (m - j)) * sin θ ^ (2 * (m - j)))
    by (rewrite <- Rpow_mult_distr, Hcs; reflexivity).
  rewrite Hk; ring.
Qed.

(* ================================================================= *)
(*  END BaselCotPoly.v.  Cbinomial + sin((2m+1)θ)=sin^(2m+1)θ·Pcot.   *)
(* ================================================================= *)
