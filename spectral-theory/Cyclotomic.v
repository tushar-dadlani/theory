(* ================================================================= *)
(*  Cyclotomic.v                                                     *)
(*                                                                    *)
(*  THE CYCLOTOMIC POLYNOMIALS Φ_n, DEFINED AND SHOWN MONIC.        *)
(*                                                                    *)
(*      Φ_1 = X − 1,                                                 *)
(*      Φ_n = (X^n − 1) / ∏_{d|n, d<n} Φ_d      (n ≥ 2),            *)
(*                                                                    *)
(*  as an actual integer polynomial (computable quotient, no choice),*)
(*  and                                                              *)
(*                                                                    *)
(*      cyclotomic_monic :  Φ_n is monic of degree φ(n)   (n ≥ 1).   *)
(*                                                                    *)
(*  Uses: PolyDivComp.pdivmod (computable division), PolyDivQuot     *)
(*  (quotient of monic by monic is monic), PolyMonic (product of     *)
(*  monics is monic), Totient (φ and Σ_{d|n} φ(d) = n).  AXIOM-FREE. *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia Arith Permutation.
Import ListNotations.
Require Import IntPoly PolyDiv PolyMonic PolyDivComp PolyDivQuot Totient.
Open Scope Z_scope.

(* proper divisors of n : the divisors strictly below n *)
Definition properdivs (n : nat) : list nat :=
  filter (fun d => (d <? n)%nat) (divisors n).

(* ----------------------------------------------------------------- *)
(*  Basic monic facts                                                *)
(* ----------------------------------------------------------------- *)
Lemma monic_one : monic [1] 0.
Proof.
  split; [ reflexivity | intros i Hi; unfold coeff; apply nth_overflow; simpl; lia ].
Qed.

Lemma coeff_pconst_hi : forall c i, (1 <= i)%nat -> coeff (pconst c) i = 0.
Proof. intros c i Hi; unfold coeff, pconst; apply nth_overflow; simpl; lia. Qed.

Lemma monic_Xn1 : forall n, (1 <= n)%nat -> monic (Xn1 n) n.
Proof.
  intros n Hn; unfold Xn1; split.
  - rewrite coeff_padd, coeff_pmonom_eq, coeff_pconst_hi by lia; ring.
  - intros i Hi; rewrite coeff_padd, coeff_pmonom_hi, coeff_pconst_hi by lia; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Totient bounds                                                   *)
(* ----------------------------------------------------------------- *)
Lemma phi_ge_1 : forall n, (1 <= n)%nat -> (1 <= phi n)%nat.
Proof.
  intros n Hn; unfold phi.
  assert (Hin : In 1%nat (filter (fun k => (Nat.gcd k n =? 1)%nat) (seq 1 n))).
  { apply filter_In; split; [ apply in_seq; lia | ].
    apply Nat.eqb_eq; cbn [Nat.gcd]; rewrite Nat.mod_1_r; reflexivity. }
  destruct (filter (fun k => (Nat.gcd k n =? 1)%nat) (seq 1 n)); [ destruct Hin | simpl; lia ].
Qed.

Lemma phi_lt : forall n, (2 <= n)%nat -> (phi n < n)%nat.
Proof.
  intros n Hn; unfold phi.
  replace (seq 1 n) with (seq 1 (n - 1) ++ [n]).
  2:{ replace n with (S (n - 1)) at 3 by lia; rewrite seq_S; f_equal; f_equal; lia. }
  rewrite filter_app; simpl.
  replace (Nat.gcd n n =? 1)%nat with false.
  2:{ rewrite Nat.gcd_diag; symmetry; apply Nat.eqb_neq; lia. }
  rewrite app_nil_r.
  pose proof (filter_length_le (fun k => (Nat.gcd k n =? 1)%nat) (seq 1 (n - 1))) as Hle.
  rewrite length_seq in Hle; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Divisor-sum plumbing                                             *)
(* ----------------------------------------------------------------- *)
Lemma fold_add_perm : forall l l', Permutation l l' ->
  fold_right Nat.add 0%nat (map phi l) = fold_right Nat.add 0%nat (map phi l').
Proof. intros l l' H; induction H; simpl; lia. Qed.

Lemma divisors_perm : forall n, (1 <= n)%nat ->
  Permutation (divisors n) (n :: properdivs n).
Proof.
  intros n Hn; apply NoDup_Permutation.
  - apply divisors_nodup.
  - constructor.
    + unfold properdivs; rewrite filter_In; intros [_ H]; apply Nat.ltb_lt in H; lia.
    + apply NoDup_filter, divisors_nodup.
  - intro x; split.
    + intro Hx; destruct (Nat.eq_dec x n) as [-> | Hne]; [ left; reflexivity | right ].
      unfold properdivs; apply filter_In; split; [ exact Hx | apply Nat.ltb_lt ].
      unfold divisors in Hx; apply filter_In in Hx; destruct Hx as [Hxs _];
        apply in_seq in Hxs; lia.
    + intros [-> | Hx].
      * unfold divisors; apply filter_In; split;
          [ apply in_seq; lia | rewrite Nat.Div0.mod_same; reflexivity ].
      * unfold properdivs in Hx; apply filter_In in Hx; tauto.
Qed.

Lemma sum_properdivs_phi : forall n, (1 <= n)%nat ->
  fold_right Nat.add 0%nat (map phi (properdivs n)) = (n - phi n)%nat.
Proof.
  intros n Hn; pose proof (totient_divisor_sum n Hn) as Hs.
  rewrite (fold_add_perm _ _ (divisors_perm n Hn)) in Hs; simpl in Hs; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  The cyclotomic recursion                                         *)
(* ----------------------------------------------------------------- *)
Fixpoint Phi_f (fuel n : nat) : poly :=
  match fuel with
  | O => [1]
  | S fl =>
      match n with
      | O => [1]
      | S O => Xn1 1
      | S (S _) =>
          let D := fold_right (fun d acc => pmul (Phi_f fl d) acc) [1] (properdivs n) in
          fst (pdivmod n (Xn1 n) D (n - phi n))
      end
  end.

Definition Phi (n : nat) : poly := Phi_f n n.

Lemma Phi_f_SS : forall fl m,
  Phi_f (S fl) (S (S m))
  = fst (pdivmod (S (S m)) (Xn1 (S (S m)))
           (fold_right (fun d acc => pmul (Phi_f fl d) acc) [1] (properdivs (S (S m))))
           (S (S m) - phi (S (S m)))).
Proof. reflexivity. Qed.

Lemma fold_pmul_ext : forall (F G : nat -> poly) l,
  (forall d, In d l -> F d = G d) ->
  fold_right (fun d acc => pmul (F d) acc) [1] l
  = fold_right (fun d acc => pmul (G d) acc) [1] l.
Proof.
  induction l as [|a l IH]; intro H; simpl; [ reflexivity | ].
  rewrite (H a (or_introl eq_refl)), (IH (fun d Hd => H d (or_intror Hd))); reflexivity.
Qed.

Lemma properdivs_lt : forall n d, In d (properdivs n) -> (d < n)%nat.
Proof.
  intros n d Hd; unfold properdivs in Hd; apply filter_In in Hd;
    destruct Hd as [_ H]; apply Nat.ltb_lt in H; exact H.
Qed.

Lemma properdivs_ge1 : forall n d, In d (properdivs n) -> (1 <= d)%nat.
Proof.
  intros n d Hd; unfold properdivs in Hd; apply filter_In in Hd; destruct Hd as [Hdiv _];
    unfold divisors in Hdiv; apply filter_In in Hdiv; destruct Hdiv as [Hs _];
    apply in_seq in Hs; lia.
Qed.

(* fuel independence: Phi_f fuel n stabilises once fuel ≥ n *)
Lemma Phi_f_indep : forall n fuel, (n <= fuel)%nat -> Phi_f fuel n = Phi_f n n.
Proof.
  intro n; induction n as [n IH] using lt_wf_ind; intros fuel Hf.
  destruct n as [|[|m]].
  - destruct fuel; reflexivity.
  - destruct fuel as [|fl]; [ lia | reflexivity ].
  - destruct fuel as [|fl]; [ lia | ].
    rewrite (Phi_f_SS fl m), (Phi_f_SS (S m) m).
    do 2 f_equal.
    apply fold_pmul_ext; intros d Hd.
    pose proof (properdivs_lt _ _ Hd) as Hdlt.
    rewrite (IH d Hdlt fl ltac:(lia)), (IH d Hdlt (S m) ltac:(lia)); reflexivity.
Qed.

(* the product of Φ_d over proper divisors is monic of degree Σ φ(d) *)
Lemma monic_fold_pmul : forall l,
  (forall d, In d l -> monic (Phi d) (phi d)) ->
  monic (fold_right (fun d acc => pmul (Phi d) acc) [1] l)
        (fold_right (fun d acc => (phi d + acc)%nat) 0%nat l).
Proof.
  induction l as [|a l IH]; intro H; simpl.
  - apply monic_one.
  - apply monic_pmul;
      [ apply H; left; reflexivity | apply IH; intros d Hd; apply H; right; exact Hd ].
Qed.

Lemma fold_phi_sum : forall l,
  fold_right (fun d acc => (phi d + acc)%nat) 0%nat l
  = fold_right Nat.add 0%nat (map phi l).
Proof.
  induction l as [|a l IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

(* ================================================================= *)
(*  MAIN THEOREM: Φ_n is monic of degree φ(n)                        *)
(* ================================================================= *)
Theorem cyclotomic_monic : forall n, (1 <= n)%nat -> monic (Phi n) (phi n).
Proof.
  intro n; induction n as [n IH] using lt_wf_ind; intro Hn.
  destruct n as [|[|m]].
  - lia.
  - unfold Phi; cbn [Phi_f]; replace (phi 1) with 1%nat by reflexivity;
      apply monic_Xn1; lia.
  - unfold Phi; rewrite (Phi_f_SS (S m) m).
    set (N := S (S m)) in *.
    set (Dprod := fold_right (fun d acc => pmul (Phi d) acc) [1] (properdivs N)).
    replace (fold_right (fun d acc => pmul (Phi_f (S m) d) acc) [1] (properdivs N))
      with Dprod.
    2:{ unfold Dprod; apply fold_pmul_ext; intros d Hd.
        pose proof (properdivs_lt _ _ Hd) as Hdlt.
        unfold Phi; rewrite (Phi_f_indep d (S m) ltac:(lia)); reflexivity. }
    assert (HD : monic Dprod (N - phi N)%nat).
    { unfold Dprod.
      replace (N - phi N)%nat
        with (fold_right (fun d acc => (phi d + acc)%nat) 0%nat (properdivs N)).
      2:{ rewrite fold_phi_sum, sum_properdivs_phi by lia; reflexivity. }
      apply monic_fold_pmul; intros d Hd.
      apply IH; [ apply properdivs_lt with (n := N); exact Hd
                | apply properdivs_ge1 with (n := N); exact Hd ]. }
    assert (Hbound : (1 <= N - phi N <= N)%nat)
      by (pose proof (phi_lt N ltac:(lia)); pose proof (phi_ge_1 N ltac:(lia)); lia).
    pose proof (monic_div_monic (Xn1 N) N Dprod (N - phi N) Hbound
                  (monic_Xn1 N ltac:(lia)) HD) as Hm.
    replace (N - (N - phi N))%nat with (phi N) in Hm
      by (pose proof (phi_lt N ltac:(lia)); lia).
    exact Hm.
Qed.

Print Assumptions cyclotomic_monic.

(* a couple of sanity values: Φ_1 = X−1, Φ_2 = X+1, Φ_3 = X²+X+1 *)
Example Phi_1_val : Phi 1 = [(-1); 1].
Proof. reflexivity. Qed.

Example Phi_2_val : Phi 2 = [1; 1].
Proof. vm_compute; reflexivity. Qed.

Example Phi_3_val : Phi 3 = [1; 1; 1].
Proof. vm_compute; reflexivity. Qed.

Example Phi_4_val : Phi 4 = [1; 0; 1].
Proof. vm_compute; reflexivity. Qed.

Example Phi_6_val : Phi 6 = [1; (-1); 1].
Proof. vm_compute; reflexivity. Qed.

(* ================================================================= *)
(*  END Cyclotomic.v                                                 *)
(*  Φ_n defined as an integer-polynomial quotient and proved monic   *)
(*  of degree φ(n).  Sanity-checked: Φ_1..Φ_6 match the classical     *)
(*  cyclotomic polynomials.  The product identity ∏_{d|n} Φ_d = X^n−1 *)
(*  (remainder zero) is the next brick.  Closed under the global      *)
(*  context (axiom-free).                                            *)
(* ================================================================= *)
