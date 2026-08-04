(* ================================================================= *)
(*  SelbergSum.v  —  toward the summatory Selberg form (Step 2d).      *)
(*                                                                    *)
(*  hyperbola_swap : the general order-swap over the hyperbola          *)
(*      Sum_{n<=N} Sum_{d|n} F d (n/d)  =  Sum_{d<=N} Sum_{m<=N/d} F d m *)
(*  (via the bijection (n,d) |-> (n/d, d) between { d|n<=N } and         *)
(*   { d*m<=N }, reusing the flatpair machinery of MuLog).  Axiom-clean.*)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Permutation.
Require Import DirichletConv VonMangoldtGlobal RealMobius MuLog SelbergSymmetry.
Import ListNotations.
Open Scope R_scope.

(* Rls over seq is the same as the finite sum Rsum 1..N used elsewhere *)
Lemma Rls_seq_cons : forall (f : nat -> R) a n,
  Rls (seq a (S n)) f = f a + Rls (seq (S a) n) f.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  the hyperbola swap                                                *)
(* ================================================================= *)

Theorem hyperbola_swap : forall (F : nat -> nat -> R) N,
  Rls (seq 1 N) (fun n => Rls (divisors n) (fun d => F d (n / d)%nat))
  = Rls (seq 1 N) (fun d => Rls (seq 1 (N / d)%nat) (fun m => F d m)).
Proof.
  intros F N.
  rewrite <- (Rls_flatpair (fun n d => F d (n / d)%nat) (fun n => divisors n) (seq 1 N)).
  rewrite <- (Rls_flatpair2 (fun m d => F d m) (fun d => seq 1 (N / d)%nat) (seq 1 N)).
  set (L1 := flatpair (fun n => divisors n) (seq 1 N)).
  set (phi := fun nd : nat * nat => ((fst nd / snd nd)%nat, snd nd)).
  transitivity (Rls (map phi L1) (fun md => F (snd md) (fst md))).
  - rewrite Rls_map; apply Rls_ext; intros nd _; unfold phi; reflexivity.
  - apply Rls_perm, NoDup_Permutation.
    + apply NoDup_map_inj;
        [ | apply NoDup_flatpair; [ apply seq_NoDup | intro; apply divisors_nodup ] ].
      intros [n d] [n' d'] Hin1 Hin2 Heq; unfold phi in Heq; cbn [fst snd] in Heq.
      injection Heq as Hnd Hdd; subst d'.
      unfold L1 in Hin1, Hin2; rewrite in_flatpair in Hin1, Hin2.
      destruct Hin1 as [_ Hdn]; destruct Hin2 as [_ Hd'n].
      apply in_divisors in Hdn; destruct Hdn as [[Hd1 _] [k Hk]].
      apply in_divisors in Hd'n; destruct Hd'n as [_ [k' Hk']].
      assert (n / d = k)%nat by (rewrite Hk, Nat.div_mul; lia).
      assert (n' / d = k')%nat by (rewrite Hk', Nat.div_mul; lia).
      rewrite H, H0 in Hnd; subst k'; rewrite Hk, Hk'; reflexivity.
    + apply NoDup_flatpair2; [ apply seq_NoDup | intro; apply seq_NoDup ].
    + intros [m d]; unfold L1; rewrite in_flatpair2; split.
      * intros Hin; apply in_map_iff in Hin; destruct Hin as [[n d'] [Hpe Hin1]].
        unfold phi in Hpe; cbn [fst snd] in Hpe; injection Hpe as Hm Hd'; subst d'.
        rewrite in_flatpair in Hin1; destruct Hin1 as [Hns Hdn].
        apply in_seq in Hns; apply in_divisors in Hdn; destruct Hdn as [[Hd1 Hdle] [k Hk]].
        assert (Hmk : (m = k)%nat) by (rewrite <- Hm, Hk, Nat.div_mul; lia).
        split; apply in_seq.
        -- lia.
        -- assert (n / d = k)%nat by (rewrite Hk, Nat.div_mul; lia).
           assert (k <= N / d)%nat by (rewrite <- H; apply Nat.Div0.div_le_mono; lia).
           lia.
      * intros [Hds Hms]; apply in_seq in Hds; apply in_seq in Hms.
        apply in_map_iff; exists ((d * m)%nat, d); split.
        -- unfold phi; cbn [fst snd]; rewrite Nat.mul_comm, Nat.div_mul by lia; reflexivity.
        -- rewrite in_flatpair; split; [ apply in_seq | apply in_divisors ].
           ++ assert (d * m <= N)%nat.
              { apply Nat.le_trans with (d * (N / d))%nat;
                  [ apply Nat.mul_le_mono_l; lia | apply Nat.Div0.mul_div_le ]. }
              lia.
           ++ split; [ split; [ lia | nia ] | exists m; ring ].
Qed.

(* ================================================================= *)
(*  the summatory Selberg sum as a hyperbola sum over  S(y)=Sum ln^2   *)
(* ================================================================= *)

Definition Slog2 (y : nat) : R := Rls (seq 1 y) (fun m => (ln (INR m)) ^ 2).

Theorem selberg_sum_eq : forall N,
  Rls (seq 1 N) Lam2
  = Rls (seq 1 N) (fun d => IZR (mu d) * Slog2 (N / d)%nat).
Proof.
  intro N.
  rewrite (Rls_ext _ Lam2
             (fun n => Rls (divisors n) (fun d => IZR (mu d) * (ln (INR (n / d)%nat)) ^ 2))
             (seq 1 N))
    by (intros n Hn; apply in_seq in Hn; apply selberg_symmetry; lia).
  rewrite (hyperbola_swap (fun d m => IZR (mu d) * (ln (INR m)) ^ 2) N).
  apply Rls_ext; intros d _; unfold Slog2; rewrite Rls_scal; reflexivity.
Qed.

Print Assumptions selberg_sum_eq.

(* ================================================================= *)
(*  the Mobius hyperbola identity  Sum_{d<=N} mu(d) floor(N/d) = 1     *)
(* ================================================================= *)

Lemma Rls_seq_const : forall (c : R) a k, Rls (seq a k) (fun _ => c) = c * INR k.
Proof.
  intros c a k; revert a; induction k as [|k IH]; intro a.
  - unfold Rls; simpl; ring.
  - rewrite Rls_seq_cons, IH, S_INR; ring.
Qed.

Theorem mu_hyperbola : forall N, (1 <= N)%nat ->
  Rls (seq 1 N) (fun d => IZR (mu d) * INR (N / d)%nat) = 1.
Proof.
  intros N HN.
  rewrite (Rls_ext _ (fun d => IZR (mu d) * INR (N / d)%nat)
             (fun d => Rls (seq 1 (N / d)%nat) (fun _ => IZR (mu d))) (seq 1 N))
    by (intros d _; rewrite Rls_seq_const; ring).
  rewrite <- (hyperbola_swap (fun d _ => IZR (mu d)) N).
  rewrite (Rls_ext _ _ (fun n => if Nat.eqb n 1 then 1 else 0) (seq 1 N))
    by (intros n Hn; apply in_seq in Hn; apply mu_real_sum; lia).
  apply Rls_sift0; [ apply seq_NoDup | apply in_seq; lia ].
Qed.

Print Assumptions mu_hyperbola.

(* ================================================================= *)
(*  END SelbergSum.v (part 1: hyperbola swap + summatory reduction)    *)
(*  Sum_{n<=N} Lam2(n) = Sum_{d<=N} mu(d) * S(floor(N/d)),             *)
(*  S(y) = Sum_{m<=y} ln^2 m.  Remaining (Step 2d): the S(y) asymptotic *)
(*  and Mobius-sum bounds giving 2N ln N + O(N).                       *)
(* ================================================================= *)
