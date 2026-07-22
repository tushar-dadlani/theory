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
From Stdlib Require Import Arith Lia PeanoNat List Reals Lra Factorial.
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
(*  TOWARD THE FINAL SQUEEZE (Chebyshev psi(x) ≍ x)                  *)
(*                                                                    *)
(*  The Chebyshev bounds follow from the order-swap identity via       *)
(*     D(N) := T(N) - 2*T(floor(N/2)) = sum_{d<=N} Lambda(d) * a_d,     *)
(*  where a_d = floor(N/d) - 2*floor(N/(2d)) = (floor(N/d)) mod 2 in    *)
(*  {0,1}, giving the sandwich  psi(N) - psi(floor N/2) <= D(N) <=      *)
(*  psi(N)  (using Lambda >= 0).  The remaining NUMERICAL input is      *)
(*  D(N) ~ N*log 2 (equivalently log of the central binomial), an       *)
(*  elementary-Stirling / central-binomial estimate -- a real-analysis  *)
(*  layer left for a dedicated pass.  Below: the combinatorial building *)
(*  blocks (Lambda >= 0, the {0,1} floor lemma, and psi).              *)
(* ================================================================= *)

Lemma spf_ge1 : forall n, 1 <= n -> 1 <= spf n.
Proof.
  intros n Hn; destruct (le_lt_dec 2 n) as [H2|H2].
  - apply Nat.le_trans with 2; [ lia | apply spf_ge2; exact H2 ].
  - assert (n = 1) by lia; subst; cbv; lia.
Qed.

Lemma ln_ge0 : forall x, (1 <= x)%R -> (0 <= ln x)%R.
Proof.
  intros x Hx; destruct (Rle_lt_or_eq_dec 1 x Hx) as [Hlt|Heq];
    [ rewrite <- ln_1; left; apply ln_increasing; lra | rewrite <- Heq, ln_1; lra ].
Qed.

(* the von Mangoldt function is nonnegative *)
Lemma Lam_nonneg : forall n, (0 <= Lam n)%R.
Proof.
  intro n; unfold Lam; destruct (is_pow n (spf n) n) eqn:E; [ | lra ].
  destruct (Nat.eq_dec n 0) as [->|Hn0]; [ simpl in E; discriminate | ].
  apply ln_ge0; replace 1%R with (INR 1) by (simpl; ring); apply le_INR, spf_ge1; lia.
Qed.

(* a_d = floor(N/d) - 2*floor(N/(2d)) = (floor(N/d)) mod 2, hence in {0,1} *)
Lemma floor_half_step : forall N d, 1 <= d ->
  (N / d - 2 * (N / (2 * d)) = (N / d) mod 2)%nat.
Proof.
  intros N d Hd; rewrite (Nat.mul_comm 2 d), <- Nat.div_div by lia.
  pose proof (Nat.div_mod (N / d) 2 ltac:(lia)); lia.
Qed.

(* the Chebyshev prime-counting function *)
Definition psi (N : nat) : R := fold_right Rplus 0%R (map Lam (seq 1 N)).

(* ----------------------------------------------------------------- *)
(*  THE FACTORIAL-LOG BRIDGE toward the central binomial             *)
(*                                                                    *)
(*  T(N) = sum_{n<=N} log n = log(N!).  Then                          *)
(*     D(N) := T(N) - 2 T(floor N/2)                                  *)
(*           = log(N!) - 2 log((floor N/2)!)                          *)
(*           = log( N! / ((floor N/2)!)^2 )  = log(central binomial),  *)
(*  reducing psi ≍ x to the elementary bounds 4^M/(2M+1) <= C(2M,M)    *)
(*  <= 4^M (row sum + unimodality), the remaining real-analysis layer. *)
(* ----------------------------------------------------------------- *)

Lemma Tlog_rec : forall N, Tlog (S N) = (Tlog N + ln (INR (S N)))%R.
Proof.
  intro N; unfold Tlog; rewrite seq_S, map_app, Rsum_app; cbn [map fold_right].
  replace (1 + N)%nat with (S N) by lia; ring.
Qed.

Lemma Tlog_eq_ln_fact : forall N, Tlog N = ln (INR (fact N)).
Proof.
  induction N as [|N IH].
  - unfold Tlog; simpl; rewrite ln_1; reflexivity.
  - rewrite Tlog_rec, IH, fact_simpl, mult_INR, ln_mult;
      [ ring | apply lt_0_INR; lia | apply lt_0_INR; apply lt_O_fact ].
Qed.

(* ================================================================= *)
(*  END Chebyshev.v                                                  *)
(*  sum_{n<=N} log n = sum_{d<=N} Lambda(d) floor(N/d) -- the          *)
(*  contour-free Dirichlet-hyperbola bridge, from sum_{d|n}Lambda=log n *)
(*  by counting multiples.  The remaining Chebyshev step (log(N!)       *)
(*  bounds + the T(N)-2T(N/2) squeeze via AbelSummation) yields         *)
(*  psi(x) ≍ x.  Uses the classical Reals axioms (quarantined).        *)
(* ================================================================= *)
