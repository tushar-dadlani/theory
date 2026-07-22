(* ================================================================= *)
(*  Chebyshev.v                                                      *)
(*                                                                    *)
(*  THE ORDER-SWAP IDENTITY -- the analytic assembly bridging the      *)
(*  global von Mangoldt identity to the summatory (Chebyshev) form.    *)
(*                                                                    *)
(*     sum_{n=1}^{N} log n  =  sum_{d=1}^{N} Lambda(d) * floor(N/d).    *)
(*                          (order_swap_identity)                     *)
(*                                                                    *)
(*  LHS = log(N!); RHS is the Dirichlet-hyperbola form.  This is the    *)
(*  contour-free analogue of Perron's formula: it re-sums the identity  *)
(*  sum_{d|n} Lambda(d) = log n (VonMangoldtGlobal) by counting, for    *)
(*  each d, how many n<=N it divides (= floor(N/d)).                    *)
(*                                                                    *)
(*  Proof: no Fubini needed -- both sides satisfy the SAME recursion    *)
(*     f (S N) = f N + dsum Lambda (S N),                              *)
(*  the key nat fact being floor((N+1)/d) = floor(N/d) + [d | N+1]      *)
(*  (div_succ_indicator).                                             *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via ln).            *)
(* ================================================================= *)

Require Import VonMangoldtGlobal.
From Stdlib Require Import Arith Lia PeanoNat List Reals Lra.
Import ListNotations.

(* going from N to S N, floor(./d) increases by [d | S N] *)
Lemma div_succ_indicator : forall d N, 1 <= d ->
  N / d + (if Nat.eqb (S N mod d) 0 then 1 else 0) = S N / d.
Proof.
  intros d N Hd.
  pose proof (Nat.div_mod (S N) d ltac:(lia)) as HSN.
  pose proof (Nat.div_mod N d ltac:(lia)) as HN.
  pose proof (Nat.mod_upper_bound (S N) d ltac:(lia)) as HSb.
  pose proof (Nat.mod_upper_bound N d ltac:(lia)) as HNb.
  destruct (Nat.eqb (S N mod d) 0) eqn:E.
  - apply Nat.eqb_eq in E; rewrite E in HSN; nia.
  - apply Nat.eqb_neq in E; nia.
Qed.

(* summing over a filtered list = summing a masked function over the list *)
Lemma filter_mask : forall (P : nat -> bool) (h : nat -> R) (l : list nat),
  fold_right Rplus 0%R (map h (filter P l))
  = fold_right Rplus 0%R (map (fun d => if P d then h d else 0%R) l).
Proof.
  intros P h; induction l as [|a l IH]; simpl; [ reflexivity | ].
  destruct (P a); simpl; rewrite IH; ring.
Qed.

(* the divisor sum as a masked sum over [1..n] *)
Lemma dsum_masked : forall n,
  dsum Lam n
  = fold_right Rplus 0%R
      (map (fun d => if Nat.eqb (n mod d) 0 then Lam d else 0%R) (seq 1 n)).
Proof.
  intro n; unfold dsum, divisors.
  rewrite (filter_mask (fun d => Nat.eqb (n mod d) 0) Lam (seq 1 n)); reflexivity.
Qed.

(* the two summatory forms *)
Definition Tlog (N : nat) : R := fold_right Rplus 0%R (map (fun n => ln (INR n)) (seq 1 N)).
Definition chsum (N : nat) : R := fold_right Rplus 0%R (map (fun d => (Lam d * INR (N / d))%R) (seq 1 N)).
Definition sumdsum (N : nat) : R := fold_right Rplus 0%R (map (fun n => dsum Lam n) (seq 1 N)).

Lemma sumdsum_rec : forall N, sumdsum (S N) = (sumdsum N + dsum Lam (S N))%R.
Proof.
  intro N; unfold sumdsum; rewrite seq_S, map_app, Rsum_app; cbn [map fold_right].
  replace (1 + N)%nat with (S N) by lia; ring.
Qed.

Lemma chsum_rec : forall N, chsum (S N) = (chsum N + dsum Lam (S N))%R.
Proof.
  intro N.
  assert (Hdsum : dsum Lam (S N) =
    (fold_right Rplus 0%R (map (fun d => if Nat.eqb (S N mod d) 0 then Lam d else 0%R) (seq 1 N))
     + Lam (S N))%R).
  { rewrite dsum_masked, seq_S, map_app, Rsum_app; cbn [map fold_right].
    replace (1 + N)%nat with (S N) by lia.
    rewrite Nat.Div0.mod_same; cbn [Nat.eqb]; ring. }
  unfold chsum.
  rewrite seq_S, map_app, Rsum_app; cbn [map fold_right].
  replace (1 + N)%nat with (S N) by lia.
  rewrite Nat.div_same by lia.
  replace (INR 1) with 1%R by (simpl; ring).
  rewrite (map_ext_in (fun d => (Lam d * INR (S N / d))%R)
             (fun d => (Lam d * INR (N / d) + (if Nat.eqb (S N mod d) 0 then Lam d else 0))%R)
             (seq 1 N)).
  2:{ intros d Hd; apply in_seq in Hd.
      rewrite <- (div_succ_indicator d N) by lia; rewrite plus_INR.
      destruct (Nat.eqb (S N mod d) 0); simpl; ring. }
  rewrite Rsum_plus, Hdsum; ring.
Qed.

Lemma order_swap : forall N, chsum N = sumdsum N.
Proof.
  induction N as [|N IH]; [ reflexivity | ].
  rewrite chsum_rec, IH; symmetry; apply sumdsum_rec.
Qed.

Lemma Tlog_eq_sumdsum : forall N, Tlog N = sumdsum N.
Proof.
  intro N; unfold Tlog, sumdsum; f_equal; apply map_ext_in.
  intros n Hn; apply in_seq in Hn; symmetry; apply vonmangoldt_identity; lia.
Qed.

(* THE ORDER-SWAP IDENTITY: log(N!) = sum_d Lambda(d) floor(N/d) *)
Theorem order_swap_identity : forall N, Tlog N = chsum N.
Proof.
  intro N; rewrite Tlog_eq_sumdsum; symmetry; apply order_swap.
Qed.

Print Assumptions order_swap_identity.

(* ================================================================= *)
(*  END Chebyshev.v                                                  *)
(*  sum_{n<=N} log n = sum_{d<=N} Lambda(d) floor(N/d) -- the          *)
(*  contour-free Dirichlet-hyperbola bridge, from sum_{d|n}Lambda=log n *)
(*  by counting multiples.  The remaining Chebyshev step (log(N!)       *)
(*  bounds + the T(N)-2T(N/2) squeeze via AbelSummation) yields         *)
(*  psi(x) ≍ x.  Uses the classical Reals axioms (quarantined).        *)
(* ================================================================= *)
