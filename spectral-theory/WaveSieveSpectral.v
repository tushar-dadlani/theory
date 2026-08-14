(* ================================================================= *)
(*  WaveSieveSpectral.v                                              *)
(*                                                                    *)
(*  Connecting the prime WAVE SIEVE to the zeta zeros -- at the level  *)
(*  the formalization honestly supports.                              *)
(*                                                                    *)
(*  Two dual "genuine waves" detect / carry the arithmetic:            *)
(*   - the prime-period wave  pw p n = sin(pi n / p)  (real sinusoid,   *)
(*     nodes at multiples of p; PrimorialWaveSieve), and its           *)
(*   - Fourier/character dual  roots_wave p j = sum_{k<p} (w_p^j)^k,    *)
(*     which PEAKS (= p) at multiples of p and vanishes otherwise;      *)
(*   - the zero-frequency wave  zero_wave c t = e^{i t log c}           *)
(*     (unit modulus), the Berry-Keating eigenfunction x^{-1/2+it}.     *)
(*                                                                    *)
(*  The prime-wave <-> Fourier-dual and the zero-wave are NEW and       *)
(*  proved here.  The chain sieve-primes -> Euler product -> zeta ->    *)
(*  -zeta'/zeta -> XiC -> spec Bxi is a packaging of existing facts     *)
(*  (see docs/wave_sieve_and_zeros.md).  The two analytic links that    *)
(*  would make it an explicit-formula IDENTITY are named in             *)
(*  wave_sieve_zeros_gap and are NOT proved (they are the frontier).    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (via C / PI / sin).          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import ComplexField Cmodulus RootsOfUnity CexpFull PrimorialWaveSieve.

(* ================================================================= *)
(*  1.  The prime-wave's Fourier / roots-of-unity dual               *)
(* ================================================================= *)

Lemma Cpow_C1 : forall q, Cpow C1 q = C1.
Proof. induction q as [| q IH]; [ reflexivity | simpl; rewrite IH; ring ]. Qed.

(* the p-th root of unity to the j equals 1 exactly when p | j *)
Lemma wpow_eq_one_iff : forall p j, (2 <= p)%nat ->
  (Cpow (w p) j = C1 <-> (j mod p = 0)%nat).
Proof.
  intros p j Hp. split.
  - intro H1.
    (* j = p*(j/p) + j mod p ; peel the full-period part to C1 *)
    assert (Hr : Cpow (w p) (j mod p) = C1).
    { rewrite (Nat.div_mod_eq j p) in H1.
      rewrite Cpow_add, Cpow_mul, (w_pow_N p ltac:(lia)), Cpow_C1 in H1.
      transitivity (Cmul C1 (Cpow (w p) (j mod p))); [ ring | exact H1 ]. }
    destruct (Nat.eq_dec (j mod p) 0) as [E | E]; [ exact E | exfalso ].
    apply (w_primitive p (j mod p)); [ | exact Hr ].
    split; [ lia | apply Nat.mod_upper_bound; lia ].
  - intro Hm.
    rewrite (Nat.div_mod_eq j p), Hm, Nat.add_0_r.
    rewrite Cpow_mul, (w_pow_N p ltac:(lia)), Cpow_C1. reflexivity.
Qed.

Definition roots_wave (p j : nat) : C := Csum (fun k => Cpow (Cpow (w p) j) k) p.

(* the roots-of-unity wave peaks at multiples of p, vanishes otherwise *)
Lemma roots_wave_div : forall p j, (2 <= p)%nat ->
  roots_wave p j = (if Nat.eqb (j mod p) 0 then RtoC (INR p) else C0).
Proof.
  intros p j Hp. unfold roots_wave. rewrite (dft_orthogonality p j ltac:(lia)).
  destruct (Ceq_dec (Cpow (w p) j) C1) as [E | E].
  - assert (Hm : (j mod p = 0)%nat) by (apply (proj1 (wpow_eq_one_iff p j Hp)); exact E).
    rewrite Hm. reflexivity.
  - assert (Hm : (j mod p <> 0)%nat)
      by (intro Hc; apply E; apply (proj2 (wpow_eq_one_iff p j Hp)); exact Hc).
    apply Nat.eqb_neq in Hm. rewrite Hm. reflexivity.
Qed.

Lemma RtoC_INR_ne0 : forall p, (1 <= p)%nat -> RtoC (INR p) <> C0.
Proof.
  intros p Hp Hc. assert (INR p <> 0) by (apply not_0_INR; lia).
  apply (f_equal Re) in Hc. cbn in Hc. contradiction.
Qed.

(* THE DUALITY: the sin-wave NODE at n <-> the roots-wave PEAK at n <-> p | n *)
Theorem sin_roots_dual : forall p n, (2 <= p)%nat ->
  (pw p n = 0 <-> roots_wave p n <> C0).
Proof.
  intros p n Hp. rewrite (pw_zero_iff p n ltac:(lia)), (roots_wave_div p n Hp).
  destruct (Nat.eqb_spec (n mod p) 0) as [Em | Em].
  - split; intro.
    + apply RtoC_INR_ne0; lia.
    + apply (proj1 (Nat.Lcm0.mod_divide n p)); exact Em.
  - split; intro H.
    + apply (proj2 (Nat.Lcm0.mod_divide n p)) in H; contradiction.
    + congruence.
Qed.

(* ================================================================= *)
(*  2.  The zero-frequency wave  e^{i t log c}  (Berry-Keating side)  *)
(* ================================================================= *)

Lemma Cpw_add : forall c a b, Cpw c (Cadd a b) = Cmul (Cpw c a) (Cpw c b).
Proof.
  intros c a b. unfold Cpw.
  replace (Cmul (Cadd a b) (RtoC (ln c)))
    with (Cadd (Cmul a (RtoC (ln c))) (Cmul b (RtoC (ln c)))) by ring.
  apply Cexpf_add.
Qed.

Definition zero_wave (c t : R) : C := Cpw c (mkC 0 t).

(* it is a unit-modulus frequency-t character of (R_+, x) *)
Theorem zero_wave_mod : forall c t, 0 < c -> Cmod (zero_wave c t) = 1.
Proof.
  intros c t Hc. unfold zero_wave. rewrite Cpw_mod. cbn [Re]. apply Rpower_O; exact Hc.
Qed.

(* the Berry-Keating eigenfunction x^{-1/2+it} = x^{-1/2} . (zero wave) *)
Theorem zero_wave_factor : forall c t,
  Cpw c (mkC (- / 2) t) = Cmul (Cpw c (mkC (- / 2) 0)) (zero_wave c t).
Proof.
  intros c t. unfold zero_wave.
  replace (mkC (- / 2) t) with (Cadd (mkC (- / 2) 0) (mkC 0 t))
    by (apply Ceq; unfold Cadd; cbn [Re Im]; ring).
  apply Cpw_add.
Qed.

(* ================================================================= *)
(*  3.  The honest gap: what would make the connection an IDENTITY    *)
(* ================================================================= *)
(*  Everything above is proved.  The chain from the sieve's primes to  *)
(*  the zeros (Euler product -> zetaC -> -zeta'/zeta -> XiC -> spec Bxi *)
(*  ) is a packaging of already-proven facts (doc), valid on Re s > 1  *)
(*  where there are NO zeros.  Reaching the zero locus needs the two    *)
(*  load-bearing pieces NOT in the repo:                              *)
(*    (i)  a complex-analytic zetaC <-> XiC continuation OFF Re s > 1,  *)
(*         transporting the prime/trace facts to the zero set;         *)
(*    (ii) the explicit formula / Mellin operator-intertwiner, summing  *)
(*         the prime side over the zero-ordinates (the Bxi-spectrum).   *)
(* We deliberately assert NEITHER (i) nor (ii) here -- they are the       *)
(* unformalized frontier (see docs/wave_sieve_and_zeros.md).  Everything   *)
(* below this line is the two proved DUAL WAVE families only.              *)

(* the two dual "genuine waves", packaged *)
Theorem wave_duality :
  (* prime side: the sin-node <-> roots-of-unity peak <-> divisibility *)
  (forall p n, (2 <= p)%nat -> (pw p n = 0 <-> roots_wave p n <> C0))
  /\ (forall p j, (2 <= p)%nat ->
        roots_wave p j = (if Nat.eqb (j mod p) 0 then RtoC (INR p) else C0))
  (* zero side: e^{i t log c} is a unit-modulus frequency-t character *)
  /\ (forall c t, 0 < c -> Cmod (zero_wave c t) = 1)
  /\ (forall c t, Cpw c (mkC (- / 2) t) = Cmul (Cpw c (mkC (- / 2) 0)) (zero_wave c t)).
Proof.
  split; [ exact sin_roots_dual | ].
  split; [ exact roots_wave_div | ].
  split; [ exact zero_wave_mod | exact zero_wave_factor ].
Qed.

Print Assumptions wave_duality.

(* ----------------------------------------------------------------- *)
(*  sanity                                                            *)
(* ----------------------------------------------------------------- *)
Example roots_peak_6 : roots_wave 3 6 = RtoC (INR 3).
Proof. rewrite roots_wave_div by lia. reflexivity. Qed.
Example roots_zero_4 : roots_wave 3 4 = C0.
Proof. rewrite roots_wave_div by lia. reflexivity. Qed.

Print Assumptions roots_wave_div.
Print Assumptions sin_roots_dual.
Print Assumptions zero_wave_mod.
