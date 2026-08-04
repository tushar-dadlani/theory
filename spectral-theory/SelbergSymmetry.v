(* ================================================================= *)
(*  SelbergSymmetry.v  —  Selberg's log^2 identity (Step 2c).          *)
(*                                                                    *)
(*  Lam2(n) := Lam(n) ln n + Sum_{d|n} Lam(d) Lam(n/d)                  *)
(*           = Sum_{d|n} mu(d) ln^2(n/d).                               *)
(*                                                                    *)
(*  Built from a general real Mobius inversion (rmobius), a second      *)
(*  divisor swap dconv_dsum (the e|d|n reindex), and the bracket        *)
(*  Sum_{d|n} Lam2(d) = ln^2 n.  Axiom-clean.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith Permutation.
Require Import DirichletConv VonMangoldtGlobal RealMobius MuLog.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  A.  general real Mobius inversion                                 *)
(* ================================================================= *)

Theorem rmobius : forall (F G : nat -> R),
  (forall m, (1 <= m)%nat -> G m = Rls (divisors m) F) ->
  forall n, (1 <= n)%nat ->
    Rls (divisors n) (fun d => IZR (mu d) * G (n / d)%nat) = F n.
Proof.
  intros F G HG n Hn.
  transitivity (Rls (divisors n)
                  (fun d => Rls (divisors (n / d)) (fun e => IZR (mu d) * F e))).
  { apply Rls_ext; intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] Hdd].
    assert (Hndd : (1 <= n / d)%nat)
      by (destruct Hdd as [k Hk]; rewrite Hk, Nat.div_mul by lia; nia).
    rewrite (HG (n / d)%nat Hndd), Rls_scal; reflexivity. }
  rewrite (div_swap (fun d e => IZR (mu d) * F e) n Hn).
  transitivity (Rls (divisors n) (fun e => if Nat.eqb (n / e) 1 then F e else 0)).
  { apply Rls_ext; intros e He; apply in_divisors in He; destruct He as [[He1 Hen] Hed].
    assert (Hnde : (1 <= n / e)%nat)
      by (destruct Hed as [k Hk]; rewrite Hk, Nat.div_mul by lia; nia).
    rewrite (Rls_ext _ _ (fun d => F e * IZR (mu d))) by (intros; ring).
    rewrite <- Rls_scal, mu_real_sum by exact Hnde.
    destruct (Nat.eqb (n / e) 1); ring. }
  rewrite (Rls_ext _ _ (fun e => if Nat.eqb e n then F e else 0)).
  - apply Rls_sift; [ apply divisors_nodup
    | apply in_divisors; repeat split; [ lia | lia | exists 1%nat; ring ] ].
  - intros e He; apply in_divisors in He; destruct He as [[He1 Hen] Hed]; destruct Hed as [k Hk].
    assert (n / e = k)%nat by (rewrite Hk, Nat.div_mul; lia).
    destruct (Nat.eqb_spec (n / e) 1) as [E1|E1]; destruct (Nat.eqb_spec e n) as [E2|E2];
      try reflexivity; subst; try (exfalso; nia).
Qed.

(* ================================================================= *)
(*  B.  the second divisor swap:  Sum_{d|n} Sum_{e|d} = Sum_{e|n} ...  *)
(* ================================================================= *)

Theorem dconv_dsum : forall (G : nat -> nat -> R) n, (1 <= n)%nat ->
  Rls (divisors n) (fun d => Rls (divisors d) (fun e => G e (d / e)%nat))
  = Rls (divisors n) (fun e => Rls (divisors (n / e)%nat) (fun f => G e f)).
Proof.
  intros G n Hn.
  rewrite <- (Rls_flatpair (fun d e => G e (d / e)%nat) (fun d => divisors d) (divisors n)).
  rewrite <- (Rls_flatpair2 (fun f e => G e f) (fun e => divisors (n / e)%nat) (divisors n)).
  set (L1 := flatpair (fun d => divisors d) (divisors n)).
  set (psi := fun de : nat * nat => ((fst de / snd de)%nat, snd de)).
  transitivity (Rls (map psi L1) (fun de => G (snd de) (fst de))).
  - rewrite Rls_map; apply Rls_ext; intros de _; unfold psi; reflexivity.
  - apply Rls_perm, NoDup_Permutation.
    + apply NoDup_map_inj;
        [ | apply NoDup_flatpair; [ apply divisors_nodup | intro; apply divisors_nodup ] ].
      intros [d e] [d' e'] Hin1 Hin2 Heq; unfold psi in Heq; cbn [fst snd] in Heq.
      injection Heq as Hde Hee; subst e'.
      unfold L1 in Hin1, Hin2; rewrite in_flatpair in Hin1, Hin2.
      destruct Hin1 as [_ Hed]; destruct Hin2 as [_ Hed'].
      apply in_divisors in Hed; apply in_divisors in Hed'.
      destruct Hed as [[He1 _] [k Hk]]; destruct Hed' as [_ [k' Hk']].
      assert (d / e = k)%nat by (rewrite Hk, Nat.div_mul; lia).
      assert (d' / e = k')%nat by (rewrite Hk', Nat.div_mul; lia).
      rewrite H, H0 in Hde; subst k'; rewrite Hk, Hk'; reflexivity.
    + apply NoDup_flatpair2; [ apply divisors_nodup | intro; apply divisors_nodup ].
    + intros [f e]; unfold L1; rewrite in_flatpair2; split.
      * intros Hin; apply in_map_iff in Hin; destruct Hin as [[d e'] [Hpe Hin1]].
        unfold psi in Hpe; cbn [fst snd] in Hpe; injection Hpe as Hf He'; subst e'.
        rewrite in_flatpair in Hin1; destruct Hin1 as [Hdn Hed].
        apply in_divisors in Hdn; destruct Hdn as [[Hd1 Hdn] [q Hq]].
        apply in_divisors in Hed; destruct Hed as [[He1 Hed] [k Hk]].
        assert (Hfk : (f = k)%nat) by (rewrite <- Hf, Hk, Nat.div_mul; lia).
        split; apply in_divisors.
        -- split; [ split; [ lia | nia ] | exists (k * q)%nat; nia ].
        -- assert (Hnek : (n / e = k * q)%nat).
           { rewrite Hq, Hk; replace (q * (k * e))%nat with ((k * q) * e)%nat by ring;
               rewrite Nat.div_mul by lia; reflexivity. }
           split; [ split; [ lia | nia ] | subst f; exists q; nia ].
      * intros [Hen Hfne].
        apply in_divisors in Hen; destruct Hen as [[He1 Hen] [m Hm]].
        apply in_divisors in Hfne; destruct Hfne as [[Hf1 Hfne] [j Hj]].
        assert (Hne : (n / e = m)%nat) by (rewrite Hm, Nat.div_mul; lia).
        apply in_map_iff; exists ((f * e)%nat, e); split.
        -- unfold psi; cbn [fst snd]; rewrite Nat.div_mul by lia; reflexivity.
        -- rewrite in_flatpair; split; apply in_divisors.
           ++ split; [ split; [ nia | nia ] | exists j; rewrite Hne in Hj; nia ].
           ++ split; [ split; [ lia | nia ] | exists f; ring ].
Qed.

Print Assumptions dconv_dsum.

(* ================================================================= *)
(*  C.  Sum_{d|n} Lam2(d) = ln^2 n,  hence  Lam2 = mu * log^2          *)
(* ================================================================= *)

Lemma Rls_add : forall A (f g : A -> R) l,
  Rls l (fun x => f x + g x) = Rls l f + Rls l g.
Proof.
  intros A f g l; induction l as [|a l IH]; [ unfold Rls; simpl; ring | ].
  rewrite !Rls_cons, IH; ring.
Qed.

Definition Lam2 (n : nat) : R :=
  Lam n * ln (INR n) + Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat).

Theorem logsq_dsum : forall n, (1 <= n)%nat ->
  Rls (divisors n) Lam2 = (ln (INR n)) ^ 2.
Proof.
  intros n Hn.
  rewrite (Rls_ext _ Lam2
             (fun d => Lam d * ln (INR d)
                       + Rls (divisors d) (fun e => Lam e * Lam (d / e)%nat)))
    by (intros; reflexivity).
  rewrite Rls_add.
  (* second sum: swap e|d|n *)
  rewrite (dconv_dsum (fun e f => Lam e * Lam f) n Hn).
  (* inner Sum_{f|(n/e)} Lam e * Lam f = Lam e * ln(n/e) *)
  rewrite (Rls_ext _
             (fun e => Rls (divisors (n / e)%nat) (fun f => Lam e * Lam f))
             (fun e => Lam e * ln (INR (n / e)%nat)) (divisors n)).
  2:{ intros e He; apply in_divisors in He; destruct He as [[He1 Hen] [k Hk]].
      assert (Hne : (1 <= n / e)%nat) by (rewrite Hk, Nat.div_mul by lia; nia).
      rewrite <- Rls_scal.
      change (Rls (divisors (n / e)%nat) Lam) with (dsum Lam (n / e)%nat).
      rewrite (vonmangoldt_identity (n / e)%nat Hne); reflexivity. }
  (* combine both sums termwise: Lam d (ln d + ln(n/d)) = Lam d ln n *)
  rewrite <- Rls_add.
  rewrite (Rls_ext _ _ (fun d => Lam d * ln (INR n))).
  2:{ intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 Hdn] [k Hk]].
      assert (Hnd : (1 <= n / d)%nat) by (rewrite Hk, Nat.div_mul by lia; nia).
      assert (Hprod : (d * (n / d) = n)%nat) by (rewrite Hk, Nat.div_mul by lia; nia).
      rewrite <- Rmult_plus_distr_l.
      rewrite <- ln_mult, <- mult_INR, Hprod by (apply lt_0_INR; lia).
      reflexivity. }
  rewrite (Rls_ext _ _ (fun d => ln (INR n) * Lam d) (divisors n)) by (intros; ring).
  rewrite <- Rls_scal.
  change (Rls (divisors n) Lam) with (dsum Lam n).
  rewrite (vonmangoldt_identity n Hn); ring.
Qed.

Theorem selberg_symmetry : forall n, (1 <= n)%nat ->
  Lam2 n = Rls (divisors n) (fun d => IZR (mu d) * (ln (INR (n / d)%nat)) ^ 2).
Proof.
  intros n Hn; symmetry.
  apply (rmobius Lam2 (fun m => (ln (INR m)) ^ 2)); [ | exact Hn ].
  intros m Hm; symmetry; apply logsq_dsum; exact Hm.
Qed.

Print Assumptions selberg_symmetry.

(* ================================================================= *)
(*  END SelbergSymmetry.v                                             *)
(*  Lam2(n) = Lam(n)ln n + (Lam*Lam)(n) = Sum_{d|n} mu(d) ln^2(n/d).    *)
(* ================================================================= *)
