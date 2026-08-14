(* ================================================================= *)
(*  PrimorialWaveSieve.v                                             *)
(*                                                                    *)
(*  A GENUINE-WAVE sieve on the primorial tower.  For each prime p     *)
(*  the "prime wave" pw p n = sin(pi n / p) is a second-order harmonic *)
(*  (y'' = -(pi/p)^2 y) that VANISHES exactly at the multiples of p.   *)
(*  The sieve wave is the product over a list of primes:               *)
(*     SWl ps n = prod_{p in ps} sin(pi n / p),                        *)
(*  starting at the period-2 wave (2^oo), multiplying in the period-3  *)
(*  wave to sieve 3 (6^oo), then period-5 (30^oo), ...  Its NODES are   *)
(*  the sieved-out numbers and its SURVIVORS are coprime to the        *)
(*  primorial; a number is prime iff it is a node of no prime-wave up   *)
(*  to sqrt(n) (it survives the wave-sieve until its own level).       *)
(*                                                                    *)
(*  Axioms: the 4 standard classical-Reals axioms (via PI/sin).        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith List Znumtheory.
Import ListNotations.
Require Import PrimorialSpectralTheory EuclidPrimes PrimeFactorizationExists.
Open Scope R_scope.

(* the prime-p wave: a genuine sinusoid, zero exactly at multiples of p *)
Definition pw (p n : nat) : R := sin (PI * INR n / INR p).

(* THE LOAD-BEARING LEMMA: pw p n = 0  <->  p | n *)
Lemma pw_zero_iff : forall p n, (1 <= p)%nat -> (pw p n = 0 <-> Nat.divide p n).
Proof.
  intros p n Hp. unfold pw.
  assert (Hpr : INR p <> 0) by (apply not_0_INR; lia).
  assert (HPI : PI <> 0) by (apply PI_neq0).
  split.
  - intro H0. apply sin_eq_0_0 in H0. destruct H0 as [k Hk].
    (* PI * INR n / INR p = IZR k * PI  ==>  INR n = IZR k * INR p *)
    assert (Hnp : INR n = IZR k * INR p).
    { apply (Rmult_eq_reg_l PI); [ | exact HPI ].
      replace (PI * INR n) with (PI * INR n / INR p * INR p) by (field; exact Hpr).
      rewrite Hk. ring. }
    (* pass to Z: Z.of_nat n = k * Z.of_nat p *)
    rewrite INR_IZR_INZ in Hnp.
    replace (IZR k * INR p) with (IZR (k * Z.of_nat p)) in Hnp
      by (rewrite mult_IZR, INR_IZR_INZ; ring).
    apply eq_IZR in Hnp.
    assert (Hk0 : (0 <= k)%Z) by (assert (0 <= Z.of_nat n)%Z by lia;
                                   assert (0 < Z.of_nat p)%Z by lia; nia).
    exists (Z.to_nat k).
    apply Nat2Z.inj. rewrite Nat2Z.inj_mul, Z2Nat.id by lia. lia.
  - intros [c Hc]. subst n.
    replace (PI * INR (c * p) / INR p) with (IZR (Z.of_nat c) * PI).
    2:{ rewrite mult_INR, INR_IZR_INZ. field. exact Hpr. }
    apply sin_eq_0_1. exists (Z.of_nat c). reflexivity.
Qed.

Lemma pw_nonzero_iff : forall p n, (1 <= p)%nat -> (pw p n <> 0 <-> ~ Nat.divide p n).
Proof.
  intros p n Hp. split; intro H; intro Hc; apply H; revert Hc; apply pw_zero_iff; exact Hp.
Qed.

(* ================================================================= *)
(*  The sieve wave: product of prime-waves over a list                *)
(* ================================================================= *)

Definition SWl (ps : list nat) (n : nat) : R :=
  fold_right Rmult 1 (map (fun p => pw p n) ps).

Lemma SWl_nil : forall n, SWl [] n = 1.
Proof. reflexivity. Qed.
Lemma SWl_cons : forall q ps n, SWl (q :: ps) n = pw q n * SWl ps n.
Proof. reflexivity. Qed.
Lemma SWl_app : forall ps qs n, SWl (ps ++ qs) n = SWl ps n * SWl qs n.
Proof.
  induction ps as [| q ps IH]; intros qs n;
    [ rewrite app_nil_l, SWl_nil; ring | ].
  rewrite <- app_comm_cons, !SWl_cons, IH; ring.
Qed.

(* survivors of the wave = numbers no listed prime divides *)
Lemma SWl_nonzero_iff : forall ps n, Forall (fun p => (1 <= p)%nat) ps ->
  (SWl ps n <> 0 <-> forall p, In p ps -> ~ Nat.divide p n).
Proof.
  induction ps as [| q ps IH]; intros n Hall.
  - rewrite SWl_nil. split; [ intros _ p [] | intros _; lra ].
  - rewrite Forall_cons_iff in Hall; destruct Hall as [Hq Hps].
    rewrite SWl_cons. split.
    + intro Hnz.
      assert (Hqnz : pw q n <> 0) by (intro Hc; apply Hnz; rewrite Hc; ring).
      assert (Hrnz : SWl ps n <> 0) by (intro Hc; apply Hnz; rewrite Hc; ring).
      intros p [<- | Hin].
      * apply (pw_nonzero_iff q n Hq); exact Hqnz.
      * apply (IH n Hps); [ exact Hrnz | exact Hin ].
    + intro Hno. intro Hc. apply Rmult_integral in Hc. destruct Hc as [Hc | Hc].
      * apply (Hno q (or_introl eq_refl)). apply (pw_zero_iff q n Hq). exact Hc.
      * revert Hc. apply (proj2 (IH n Hps)). intros p Hin. apply Hno; right; exact Hin.
Qed.

(* ================================================================= *)
(*  The tower narrative: 2^oo -> sieve 3 -> 6^oo -> sieve 5 -> 30^oo   *)
(* ================================================================= *)

(* the primorial-prime list gains the next prime at the end *)
Lemma pp_snoc : forall k,
  primorial_primes (S k) = primorial_primes k ++ (kth_prime (S k) :: nil).
Proof.
  intro k. unfold primorial_primes. rewrite seq_S, map_app. simpl. reflexivity.
Qed.

(* the base level is the period-2 wave *)
Lemma SW_base : forall n, SWl (primorial_primes 0) n = pw 2 n.
Proof.
  intro n. rewrite primorial_primes_0. rewrite SWl_cons, SWl_nil. ring.
Qed.

(* each step multiplies in the next prime's wave (sieves the next prime) *)
Lemma SW_step : forall k n,
  SWl (primorial_primes (S k)) n = SWl (primorial_primes k) n * pw (kth_prime (S k)) n.
Proof.
  intros k n. rewrite pp_snoc, SWl_app, SWl_cons, SWl_nil. ring.
Qed.

(* ================================================================= *)
(*  Eratosthenes: a composite has a prime factor q with q*q <= n      *)
(* ================================================================= *)
Lemma composite_has_sqrt_factor : forall n, (1 < n)%nat -> ~ prime (Z.of_nat n) ->
  exists q, prime (Z.of_nat q) /\ (q * q <= n)%nat /\ Nat.divide q n.
Proof.
  intros n Hn Hnp.
  assert (Hd : exists d, (1 < d < n)%nat /\ Nat.divide d n).
  { destruct (not_prime_divide (Z.of_nat n) ltac:(lia) Hnp) as [p [Hpr Hpd]].
    exists (Z.to_nat p). split; [ lia | ].
    apply Zdiv_nat. rewrite Z2Nat.id by lia. exact Hpd. }
  destruct Hd as [d [Hd Hddiv]]. destruct Hddiv as [c Hc].   (* n = c * d *)
  destruct (le_gt_dec (d * d) n) as [Hle | Hgt].
  - destruct (nat_prime_divisor d ltac:(lia)) as [q [Hq Hqd]].
    assert (Hqled : (q <= d)%nat) by (apply Nat.divide_pos_le; [ lia | exact Hqd ]).
    exists q; split; [ exact Hq | split ].
    + nia.
    + apply (Nat.divide_trans q d n); [ exact Hqd | exists c; exact Hc ].
  - assert (Hcd : (c < d)%nat) by nia.
    assert (Hc2 : (2 <= c)%nat) by nia.
    destruct (nat_prime_divisor c ltac:(lia)) as [q [Hq Hqc]].
    assert (Hqlec : (q <= c)%nat) by (apply Nat.divide_pos_le; [ lia | exact Hqc ]).
    exists q; split; [ exact Hq | split ].
    + nia.
    + apply (Nat.divide_trans q c n); [ exact Hqc | exists d; rewrite Hc; ring ].
Qed.

(* ================================================================= *)
(*  PRIME DETECTION: n is prime iff it is a node of no prime-wave      *)
(*  up to sqrt(n) -- it survives the wave-sieve until its own level.   *)
(* ================================================================= *)
Theorem primes_via_wave : forall n, (1 < n)%nat ->
  (prime (Z.of_nat n) <-> forall p, prime (Z.of_nat p) -> (p * p <= n)%nat -> pw p n <> 0).
Proof.
  intros n Hn. split.
  - intros Hprime p Hp Hpp.
    assert (Hp2 : (2 <= p)%nat) by (generalize (prime_ge_2 _ Hp); lia).
    apply (pw_nonzero_iff p n); [ lia | ]. intro Hpd.
    assert (Hpdz : (Z.of_nat p | Z.of_nat n)%Z)
      by (destruct Hpd as [c ->]; exists (Z.of_nat c); rewrite Nat2Z.inj_mul; ring).
    destruct (prime_divisors _ Hprime _ Hpdz) as [E | [E | [E | E]]]; try lia.
    assert (p = n) by lia. nia.
  - intros Hno. destruct (prime_dec (Z.of_nat n)) as [Hp | Hnp]; [ exact Hp | exfalso ].
    destruct (composite_has_sqrt_factor n Hn Hnp) as [q [Hq [Hqq Hqd]]].
    assert (Hq1 : (1 <= q)%nat) by (generalize (prime_ge_2 _ Hq); lia).
    apply (Hno q Hq Hqq). apply (pw_zero_iff q n Hq1); exact Hqd.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                    *)
(* ----------------------------------------------------------------- *)
Theorem primorial_wave_sieve :
  (* the prime wave vanishes exactly at multiples of p *)
  (forall p n, (1 <= p)%nat -> (pw p n = 0 <-> Nat.divide p n))
  (* survivors of the sieve wave = numbers no listed prime divides *)
  /\ (forall ps n, Forall (fun p => (1 <= p)%nat) ps ->
        (SWl ps n <> 0 <-> forall p, In p ps -> ~ Nat.divide p n))
  (* the tower: base is the 2-wave, each step sieves the next prime *)
  /\ (forall n, SWl (primorial_primes 0) n = pw 2 n)
  /\ (forall k n, SWl (primorial_primes (S k)) n
        = SWl (primorial_primes k) n * pw (kth_prime (S k)) n)
  (* prime detection: n prime iff a node of no prime-wave up to sqrt n *)
  /\ (forall n, (1 < n)%nat ->
        (prime (Z.of_nat n) <-> forall p, prime (Z.of_nat p) -> (p * p <= n)%nat -> pw p n <> 0)).
Proof.
  split; [ exact pw_zero_iff | ].
  split; [ exact SWl_nonzero_iff | ].
  split; [ exact SW_base | ].
  split; [ exact SW_step | exact primes_via_wave ].
Qed.

(* sanity: the 2-wave has a node at 4 (even), the 3-wave does not *)
Example pw2_node4 : pw 2 4 = 0.
Proof. apply pw_zero_iff; [ lia | exists 2%nat; reflexivity ]. Qed.
Example pw3_no_node4 : pw 3 4 <> 0.
Proof. apply pw_nonzero_iff; [ lia | intros [c Hc]; lia ]. Qed.
(* the 6-sieve wave: nonzero at 5 (coprime to 6), zero at 6 *)
Example sw6_survive5 : SWl (2%nat :: 3%nat :: nil) 5 <> 0.
Proof.
  apply SWl_nonzero_iff.
  - repeat constructor; lia.
  - intros p [<- | [<- | []]]; intros [c Hc]; lia.
Qed.
Example sw6_node6 : SWl (2%nat :: 3%nat :: nil) 6 = 0.
Proof.
  assert (H : pw 2 6 = 0) by (apply pw_zero_iff; [ lia | exists 3%nat; reflexivity ]).
  rewrite SWl_cons, H; ring.
Qed.

Print Assumptions primorial_wave_sieve.
