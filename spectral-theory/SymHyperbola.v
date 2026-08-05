(* ================================================================= *)
(*  SymHyperbola.v  —  the symmetric hyperbola swap (Step 2d, v3c).     *)
(*                                                                    *)
(*  The Fubini swap over the region { (d,m) : d*m <= N }:               *)
(*      Sum_{d<=N} Sum_{m<=N/d} F d m  =  Sum_{m<=N} Sum_{d<=N/m} F d m. *)
(*  Derived from hyperbola_swap applied twice (once to F, once to its    *)
(*  transpose) and the divisor involution  d |-> n/d  on divisors(n):    *)
(*      Sum_{d|n} F d (n/d)  =  Sum_{d|n} F (n/d) d.                     *)
(*  This is the engine that turns  Sum_d (mu(d)/d) Sum_{m<=N/d} b(m)     *)
(*  into  Sum_m b(m) * (Sum_{d<=N/m} mu(d)/d),  making the Selberg       *)
(*  defect sum O(1) with no Abel summation and no limits.  Axiom-clean.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List Permutation.
Require Import VonMangoldtGlobal RealMobius MuLog SelbergSum.
Import ListNotations.
Open Scope R_scope.

Lemma div_complement_inv : forall n d k,
  (1 <= d)%nat -> (1 <= k)%nat -> n = (k * d)%nat -> (n / (n / d))%nat = d.
Proof.
  intros n d k Hd Hk Hn.
  assert (H1 : (n / d = k)%nat) by (rewrite Hn, Nat.div_mul; lia).
  rewrite H1, Hn, (Nat.mul_comm k d), Nat.div_mul; lia.
Qed.

Lemma divisors_involution : forall n, (1 <= n)%nat ->
  Permutation (divisors n) (map (fun d => (n / d)%nat) (divisors n)).
Proof.
  intros n Hn; apply NoDup_Permutation; [ apply divisors_nodup | | ].
  - apply NoDup_map_inj; [ | apply divisors_nodup ].
    intros d d' Hd Hd' Heq.
    apply in_divisors in Hd; apply in_divisors in Hd'.
    destruct Hd as [[Hd1 Hdn] [k Hk]]; destruct Hd' as [[Hd'1 Hd'n] [k' Hk']].
    assert (Hkd : (n / d = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
    assert (Hkd' : (n / d' = k')%nat) by (rewrite Hk', Nat.div_mul; lia).
    rewrite Hkd, Hkd' in Heq; subst k'; nia.
  - intros a; split.
    + intros Ha; apply in_divisors in Ha; destruct Ha as [[Ha1 Han] [k Hk]].
      apply in_map_iff; exists (n / a)%nat; split.
      * apply (div_complement_inv n a k); [ lia | nia | exact Hk ].
      * apply in_divisors; assert (Hka : (n / a = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
        rewrite Hka; repeat split; [ nia | nia | exists a; nia ].
    + intros Ha; apply in_map_iff in Ha; destruct Ha as [d [Hd Hdin]].
      apply in_divisors in Hdin; destruct Hdin as [[Hd1 Hdn] [k Hk]].
      apply in_divisors; subst a;
        assert (Hkd : (n / d = k)%nat) by (rewrite Hk, Nat.div_mul; lia).
      rewrite Hkd; repeat split; [ nia | nia | exists d; nia ].
Qed.

(* the divisor involution at the sum level *)
Lemma dsum_involution : forall (F : nat -> nat -> R) n, (1 <= n)%nat ->
  Rls (divisors n) (fun d => F d (n / d)%nat)
  = Rls (divisors n) (fun d => F (n / d)%nat d).
Proof.
  intros F n Hn.
  rewrite (Rls_perm _ (fun d => F d (n / d)%nat) (divisors n)
             (map (fun e => (n / e)%nat) (divisors n)) (divisors_involution n Hn)).
  rewrite Rls_map.
  apply Rls_ext; intros e He; apply in_divisors in He;
    destruct He as [[He1 Hen] [k Hk]].
  rewrite (div_complement_inv n e k ltac:(lia) ltac:(nia) Hk); reflexivity.
Qed.

(* the symmetric hyperbola swap *)
Theorem hyperbola_swap_sym : forall (F : nat -> nat -> R) N,
  Rls (seq 1 N) (fun d => Rls (seq 1 (N / d)%nat) (fun m => F d m))
  = Rls (seq 1 N) (fun m => Rls (seq 1 (N / m)%nat) (fun d => F d m)).
Proof.
  intros F N.
  rewrite <- (hyperbola_swap F N).
  rewrite <- (hyperbola_swap (fun a b => F b a) N).
  apply Rls_ext; intros n Hn; apply in_seq in Hn.
  apply (dsum_involution F n ltac:(lia)).
Qed.

Print Assumptions hyperbola_swap_sym.

(* ================================================================= *)
(*  END SymHyperbola.v                                                *)
(*  Sum_{d<=N} Sum_{m<=N/d} F d m = Sum_{m<=N} Sum_{d<=N/m} F d m.      *)
(* ================================================================= *)
