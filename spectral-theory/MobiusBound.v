(* ================================================================= *)
(*  MobiusBound.v  —  |mu(n)| <= 1   (Step 2d, v: the error-control     *)
(*                    foundation for the Selberg main-term assembly).   *)
(*                                                                    *)
(*  Every error bound in the summed Selberg formula weights a remainder  *)
(*  by mu(d); to sum |mu(d)|*|error| <= |error| we need mu in {-1,0,1}.  *)
(*                                                                    *)
(*  Proof: mu is multiplicative (mu_mult_prod on coprimes).  On a prime  *)
(*  power p^a (a>=1),  mu(p^a) = deps(p^a) - deps(p^{a-1}) in {-1,0},    *)
(*  since Sum_{d|p^a} mu(d) = [p^a=1] (Sigma_mu_div) telescopes over the  *)
(*  divisors {p^0,...,p^a} (divisors_primepow).  A coprime prime-power   *)
(*  factorization induction (pval_fuel, spf) then gives |mu(n)| <= 1,    *)
(*  mirroring the vonmangoldt_identity assembly.  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith Lia List Permutation Wf_nat Znumtheory.
Require Import HopfGroupTensor DirichletConv DirichletMult VonMangoldtGlobal.
Import ListNotations.
Local Open Scope nat_scope.

Lemma sumf_nil : forall (F : nat -> Z), sumf (@nil nat) F = 0%Z.
Proof. reflexivity. Qed.

Lemma sumf_app : forall (l1 l2 : list nat) (F : nat -> Z),
  sumf (l1 ++ l2) F = (sumf l1 F + sumf l2 F)%Z.
Proof.
  induction l1 as [|a l1 IH]; intros l2 F; [ reflexivity | ].
  cbn [app]; rewrite !sumf_cons, IH; ring.
Qed.

Section PrimePow.
Variable p : nat.
Hypothesis Hp : nprime p.

(* Sum_{j=0}^k mu(p^j) = [p^k = 1] *)
Lemma Ssum_eq : forall k, sumf (map (fun j => p ^ j) (seq 0 (S k))) mu = deps (p ^ k).
Proof.
  intro k.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hpk : (1 <= p ^ k)%nat).
  { assert (p ^ k <> 0)%nat by (apply Nat.pow_nonzero; lia); lia. }
  rewrite <- (sumf_perm _ _ mu (divisors_primepow p k Hp)).
  apply Sigma_mu_div; exact Hpk.
Qed.

(* the telescoped prime-power value *)
Lemma mu_ppow_val : forall a, (1 <= a)%nat -> mu (p ^ a) = (deps (p ^ a) - deps (p ^ (a - 1)))%Z.
Proof.
  intros a Ha; destruct a as [|a']; [ lia | ].
  replace (S a' - 1)%nat with a' by lia.
  pose proof (Ssum_eq (S a')) as H1.
  pose proof (Ssum_eq a') as H0.
  rewrite seq_S, map_app, sumf_app, Nat.add_0_l in H1.
  replace (map (fun j => p ^ j) [S a']) with [p ^ S a'] in H1 by reflexivity.
  rewrite H0, sumf_cons, sumf_nil in H1.
  lia.
Qed.

Lemma mu_ppow_bound : forall a, (1 <= a)%nat -> (-1 <= mu (p ^ a) <= 1)%Z.
Proof.
  intros a Ha; rewrite (mu_ppow_val a Ha).
  unfold deps; destruct (p ^ a =? 1)%nat; destruct (p ^ (a - 1) =? 1)%nat; lia.
Qed.

End PrimePow.

(* the Mobius bound, by coprime prime-power factorization *)
Theorem mu_abs_le_1 : forall n, (1 <= n)%nat -> (-1 <= mu n <= 1)%Z.
Proof.
  intro n; induction n as [n IH] using (well_founded_induction lt_wf); intro Hn.
  destruct (Nat.eq_dec n 1) as [->|Hn1].
  - rewrite mu_1; lia.
  - assert (Hn2 : 2 <= n) by lia.
    set (p := spf n).
    assert (Hp : nprime p) by (apply spf_nprime; exact Hn2).
    assert (Hp2 : 2 <= p) by (destruct Hp; lia).
    destruct (pval_fuel n p n Hp2 Hn (le_n n)) as [a [m [Heq [Hpm Hm]]]].
    assert (Ha1 : 1 <= a).
    { destruct a as [|a']; [ exfalso | lia ].
      apply Hpm; assert (Hnm : m = n) by (rewrite Heq; simpl; lia).
      rewrite Hnm; apply spf_divides; exact Hn2. }
    assert (Hcop : Nat.gcd (p ^ a) m = 1) by (apply coprime_ppow_pfree; assumption).
    assert (Hpa1 : 1 <= p ^ a)
      by (rewrite <- (Nat.pow_1_l a); apply Nat.pow_le_mono_l; lia).
    assert (Hpa2 : 2 <= p ^ a)
      by (apply Nat.le_trans with (p ^ 1);
          [ rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia ]).
    assert (Hmlt : (m < n)%nat) by (rewrite Heq; nia).
    rewrite Heq, (mu_mult_prod (p ^ a) m Hpa1 Hm Hcop).
    pose proof (mu_ppow_bound p Hp a Ha1) as Hb1.
    pose proof (IH m Hmlt Hm) as Hb2.
    assert (E : (mu (p ^ a) = -1 \/ mu (p ^ a) = 0 \/ mu (p ^ a) = 1)%Z) by lia.
    assert (F : (mu m = -1 \/ mu m = 0 \/ mu m = 1)%Z) by lia.
    destruct E as [E|[E|E]]; destruct F as [F|[F|F]]; rewrite E, F; lia.
Qed.

Print Assumptions mu_abs_le_1.

(* ================================================================= *)
(*  END MobiusBound.v  —  -1 <= mu(n) <= 1.                            *)
(* ================================================================= *)
