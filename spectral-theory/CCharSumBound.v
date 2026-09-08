(* ================================================================= *)
(*  CCharSumBound.v  --  partial character sums are bounded.          *)
(*                                                                    *)
(*  For a NON-PRINCIPAL character chi mod a prime p,                   *)
(*                                                                    *)
(*      | sum_{n=1}^{N} chi(n) |  <=  p    for every N.                *)
(*                                                                    *)
(*  This is the input that lets Abel summation push L(s,chi) from      *)
(*  Re s > 1 down to Re s > 0.  The repo already has the vanishing of  *)
(*  ONE period (GaussSum.char_sum_zero) and one-step periodicity       *)
(*  (DirichletModP.dchar_periodic); what is missing, and is built      *)
(*  here, is the consequence: a full period sums to zero at ANY        *)
(*  offset, hence the partial sum is p-periodic, hence bounded by its  *)
(*  values on the first period.                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus RootsOfUnity ZmodOrder DirichletModP
        CharModulus GaussSum.
Import ListNotations.
Open Scope R_scope.

(* triangle inequality for Sf *)
Lemma Cmod_Sf_le : forall (f : nat -> C) l,
  Cmod (Sf f l) <= fold_right Rplus 0 (map (fun x => Cmod (f x)) l).
Proof.
  intros f l. induction l as [| x l IH]; cbn [map fold_right].
  - rewrite Sf_empty, (proj2 (Cmod0 C0) eq_refl). apply Rle_refl.
  - rewrite Sf_cons. eapply Rle_trans; [ apply Cmod_triangle | ].
    apply Rplus_le_compat_l. exact IH.
Qed.

Lemma Sf_app : forall (f : nat -> C) l1 l2,
  Sf f (l1 ++ l2) = Cadd (Sf f l1) (Sf f l2).
Proof.
  intros f l1 l2. induction l1 as [| x l1 IH]; cbn [app].
  - rewrite Sf_empty. ring.
  - rewrite !Sf_cons, IH. ring.
Qed.

Section CharSum.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.

Lemma Hp2 : (2 <= p)%nat.
Proof. destruct Hp; lia. Qed.

(* the character vanishes at the modulus *)
Lemma dchar_at_p : dchar p g A p = C0.
Proof.
  apply dchar_zero. exists 1%nat. lia.
Qed.

(* a full period, starting at 1, sums to zero *)
Lemma period_zero_1 : Sf (dchar p g A) (seq 1 p) = C0.
Proof.
  pose proof Hp2 as H2.
  replace p with (S (p - 1)) at 2 by lia.
  rewrite seq_S, Sf_app.
  rewrite (char_sum_zero p Hp g Hg Hord A HA).
  replace (1 + (p - 1))%nat with p by lia.
  rewrite Sf_cons, Sf_empty, dchar_at_p. ring.
Qed.

(* a full period starting anywhere sums to zero *)
Lemma period_zero : forall k, Sf (dchar p g A) (seq (S k) p) = C0.
Proof.
  pose proof Hp2 as H2.
  induction k as [| k IH].
  - exact period_zero_1.
  - (* seq (S (S k)) p = seq (S (S k)) (p-1) ++ [S k + p]  and
       seq (S k) p     = S k :: seq (S (S k)) (p-1)                *)
    assert (E1 : seq (S k) p = S k :: seq (S (S k)) (p - 1)).
    { replace p with (S (p - 1)) at 1 by lia. cbn [seq]. reflexivity. }
    assert (E2 : seq (S (S k)) p
                 = seq (S (S k)) (p - 1) ++ [S (S k) + (p - 1)]%nat).
    { replace p with (S (p - 1)) at 1 by lia. apply seq_S. }
    rewrite E2, Sf_app.
    rewrite E1, Sf_cons in IH.
    rewrite Sf_cons, Sf_empty.
    replace (S (S k) + (p - 1))%nat with (S k + p)%nat by lia.
    rewrite (dchar_periodic p g A (S k)).
    (* IH : chi(S k) + Sf (seq (S (S k)) (p-1)) = C0 *)
    transitivity (Cadd (dchar p g A (S k))
                       (Sf (dchar p g A) (seq (S (S k)) (p - 1))));
      [ ring | exact IH ].
Qed.

Definition PS (N : nat) : C := Sf (dchar p g A) (seq 1 N).

Lemma PS_period : forall N, PS (N + p) = PS N.
Proof.
  intro N. unfold PS.
  assert (E : seq 1 (N + p) = seq 1 N ++ seq (S N) p).
  { rewrite seq_app. reflexivity. }
  rewrite E, Sf_app, (period_zero N). ring.
Qed.

(* on the first period, the trivial bound *)
Lemma PS_small : forall N, (N <= p)%nat -> Cmod (PS N) <= INR p.
Proof.
  intros N HN. unfold PS.
  eapply Rle_trans; [ apply Cmod_Sf_le | ].
  apply Rle_trans with (fold_right Rplus 0 (map (fun _ : nat => 1) (seq 1 N))).
  - assert (Hle : forall l : list nat,
             fold_right Rplus 0 (map (fun x => Cmod (dchar p g A x)) l)
             <= fold_right Rplus 0 (map (fun _ : nat => 1) l)).
    { induction l as [| x l IH]; cbn [map fold_right]; [ lra | ].
      pose proof (Cmod_dchar_le p g A x). lra. }
    apply Hle.
  - assert (Hcount : forall (st n : nat),
             fold_right Rplus 0 (map (fun _ : nat => 1) (seq st n)) = INR n).
    { intros st n. revert st. induction n as [| n IH]; intro st;
        cbn [seq map fold_right]; [ reflexivity | ].
      rewrite IH, S_INR. ring. }
    rewrite Hcount. apply le_INR. exact HN.
Qed.

(* THE BOUND *)
Theorem PS_bound : forall N, Cmod (PS N) <= INR p.
Proof.
  pose proof Hp2 as H2.
  intro N. induction N as [N IH] using lt_wf_ind.
  destruct (le_lt_dec N p) as [Hle | Hgt].
  - apply PS_small; exact Hle.
  - assert (E : N = ((N - p) + p)%nat) by lia.
    rewrite E, PS_period. apply IH. lia.
Qed.

End CharSum.

Print Assumptions PS_bound.

(* ================================================================= *)
(*  END CCharSumBound.v                                               *)
(* ================================================================= *)
