(* ================================================================= *)
(*  VonMangoldtGlobal.v                                              *)
(*                                                                    *)
(*  THE GLOBAL VON MANGOLDT IDENTITY:  sum_{d | n} Lambda(d) = log n.  *)
(*                                                                    *)
(*  This globalises VonMangoldt (which proved Lambda = mu * log per    *)
(*  single prime) to a genuine arithmetic function Lambda : nat -> R    *)
(*  over ALL n, and proves the fundamental identity                    *)
(*     sum over divisors d of n of Lambda(d) = ln n.                   *)
(*  It is the arithmetic crux of the contour-free prime bridge (the     *)
(*  input to Chebyshev's psi(x) ~ x, alongside AbelSummation).         *)
(*                                                                    *)
(*  Everything stays in nat (Nat.gauss for coprimality) + R (for ln);  *)
(*  no complex analysis, no Z.  Uses the classical Reals axioms         *)
(*  (quarantined) for ln.                                             *)
(*                                                                    *)
(*  CHECKPOINT A (this file, part 1): the smallest-prime-factor spf,    *)
(*  nat-primality, the divisor sum dsum, and its Permutation-           *)
(*  invariance.  Lambda, its characterisation, and the identity build   *)
(*  on top.                                                           *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia PeanoNat List Permutation Reals Lra.
Import ListNotations.

(* ================================================================= *)
(*  1.  SMALLEST PRIME FACTOR                                         *)
(* ================================================================= *)

Fixpoint least_div (fuel k n : nat) : nat :=
  match fuel with
  | O => n
  | S f => if Nat.eqb (n mod k) 0 then k else least_div f (S k) n
  end.

Definition spf (n : nat) : nat := least_div n 2 n.

Lemma least_div_divides : forall fuel k n,
  2 <= k -> k <= n -> (n - k < fuel) -> Nat.divide (least_div fuel k n) n.
Proof.
  induction fuel as [|f IH]; intros k n Hk Hkn Hf; [ lia | ].
  simpl. destruct (Nat.eqb (n mod k) 0) eqn:E.
  - apply Nat.eqb_eq, Nat.Lcm0.mod_divide in E; exact E.
  - destruct (Nat.eq_dec k n) as [->|Hne];
      [ rewrite Nat.Div0.mod_same in E; discriminate | apply IH; lia ].
Qed.

Lemma least_div_least : forall fuel k n j,
  2 <= k -> k <= n -> k <= j -> j < least_div fuel k n -> (n - k < fuel) -> ~ Nat.divide j n.
Proof.
  induction fuel as [|f IH]; intros k n j Hk Hkn Hkj Hjld Hf; [ simpl in Hjld; lia | ].
  simpl in Hjld. destruct (Nat.eqb (n mod k) 0) eqn:E; [ lia | ].
  assert (Hklt : k < n)
    by (destruct (Nat.eq_dec k n) as [->|]; [ rewrite Nat.Div0.mod_same in E; discriminate | lia ]).
  destruct (Nat.eq_dec j k) as [->|Hne].
  - intro Hd; apply Nat.Lcm0.mod_divide in Hd; rewrite Hd in E; discriminate.
  - apply (IH (S k) n j); lia.
Qed.

Lemma least_div_ge2 : forall fuel k n, 2 <= k -> 2 <= n -> 2 <= least_div fuel k n.
Proof.
  induction fuel as [|f IH]; intros k n Hk Hn; simpl; [ lia | ].
  destruct (Nat.eqb (n mod k) 0); [ lia | apply IH; lia ].
Qed.

Lemma spf_divides : forall n, 2 <= n -> Nat.divide (spf n) n.
Proof. intros n Hn; unfold spf; apply least_div_divides; lia. Qed.

Lemma spf_ge2 : forall n, 2 <= n -> 2 <= spf n.
Proof. intros n Hn; unfold spf; apply least_div_ge2; lia. Qed.

Lemma spf_least : forall n e, 2 <= n -> 2 <= e -> e < spf n -> ~ Nat.divide e n.
Proof. intros n e Hn He Helt; unfold spf in *; apply (least_div_least n 2 n e); lia. Qed.

(* ================================================================= *)
(*  2.  NAT PRIMALITY, and spf is prime                              *)
(* ================================================================= *)

Definition nprime (p : nat) : Prop :=
  2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.

Lemma spf_nprime : forall n, 2 <= n -> nprime (spf n).
Proof.
  intros n Hn; split; [ apply spf_ge2; exact Hn | ].
  intros d Hd.
  assert (Hp2 : 2 <= spf n) by (apply spf_ge2; exact Hn).
  assert (Hdle : d <= spf n) by (apply Nat.divide_pos_le; [ lia | exact Hd ]).
  assert (Hd1 : 1 <= d) by (destruct d; [ destruct Hd as [x Hx]; lia | lia ]).
  destruct (Nat.eq_dec d 1) as [->|Hne1]; [ left; reflexivity | ].
  destruct (Nat.eq_dec d (spf n)) as [->|Hnep]; [ right; reflexivity | exfalso ].
  (* 2 <= d < spf n and d | spf n | n  -> d | n, contradicting minimality *)
  apply (spf_least n d Hn); [ lia | lia | ].
  apply Nat.divide_trans with (spf n); [ exact Hd | apply spf_divides; exact Hn ].
Qed.

(* ================================================================= *)
(*  3.  DIVISORS AND THE DIVISOR SUM                                 *)
(* ================================================================= *)

Definition divisors (n : nat) : list nat :=
  filter (fun d => Nat.eqb (n mod d) 0) (seq 1 n).

Lemma in_divisors : forall n d,
  In d (divisors n) <-> (1 <= d <= n /\ Nat.divide d n).
Proof.
  intros n d; unfold divisors; rewrite filter_In, in_seq; split.
  - intros [[H1 H2] Hmod]; split; [ lia | ].
    apply Nat.Lcm0.mod_divide; apply Nat.eqb_eq; exact Hmod.
  - intros [[H1 H2] Hdvd]; split; [ lia | ].
    apply Nat.eqb_eq, Nat.Lcm0.mod_divide; exact Hdvd.
Qed.

Lemma divisors_nodup : forall n, NoDup (divisors n).
Proof. intro n; unfold divisors; apply NoDup_filter, seq_NoDup. Qed.

Definition dsum (f : nat -> R) (n : nat) : R := fold_right Rplus 0%R (map f (divisors n)).

(* fold_right Rplus is invariant under permutation *)
Lemma Rsum_perm : forall (l l' : list R), Permutation l l' ->
  fold_right Rplus 0%R l = fold_right Rplus 0%R l'.
Proof.
  intros l l' H; induction H; simpl;
    [ reflexivity | rewrite IHPermutation; reflexivity
    | ring | rewrite IHPermutation1, IHPermutation2; reflexivity ].
Qed.

Lemma dsum_perm : forall (f : nat -> R) (l l' : list nat), Permutation l l' ->
  fold_right Rplus 0%R (map f l) = fold_right Rplus 0%R (map f l').
Proof.
  intros f l l' H; exact (Rsum_perm (map f l) (map f l') (Permutation_map f H)).
Qed.

Print Assumptions spf_nprime.

(* ================================================================= *)
(*  END VonMangoldtGlobal.v (checkpoint A)                           *)
(*  spf (smallest prime factor, proved prime), the divisor sum dsum,   *)
(*  and its permutation-invariance -- the foundation for Lambda and    *)
(*  the identity sum_{d|n} Lambda(d) = log n.                          *)
(* ================================================================= *)
