(* ================================================================= *)
(*  DirichletZetaSquare.v                                            *)
(*                                                                    *)
(*  ZETA SQUARED, at the Dirichlet-coefficient level (axiom-free).    *)
(*                                                                    *)
(*  In this development a Dirichlet series is represented by its      *)
(*  coefficient sequence (an arithmetic function ℕ→ℤ under ∗).        *)
(*  The dictionary:                                                   *)
(*                                                                    *)
(*        ζ(s)      ↔  done   (constant 1)                            *)
(*        1/ζ(s)    ↔  mu     (Möbius)                                *)
(*        ζ(s)²     ↔  done ∗ done  =  dtau  =  τ  (divisor count)    *)
(*        ζ(s)/ζ(2s) ↔  |mu|  (squarefree indicator)                 *)
(*        ζ(s)²/ζ(2s) ↔  |mu| ∗ done                                 *)
(*                                                                    *)
(*  Part A makes ζ² ↔ τ explicit.  Parts B–D prove the genuinely new  *)
(*  coefficient identity for ζ(s)²/ζ(2s):                             *)
(*                                                                    *)
(*        (|mu| ∗ 1)(n)  =  2^ω(n)                                    *)
(*                                                                    *)
(*  i.e. the number of squarefree divisors of n equals 2 to the       *)
(*  number of its distinct prime factors.  AXIOM-FREE.               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Import ListNotations.
Require Import HopfGroupTensor Totient DirichletConv DirichletMult DirichletDivisor
        DirichletPPow DirichletPeel DirichletVexpCoprime DirichletVonMangoldtGen JacobiRHS.
Open Scope Z_scope.

(* ================================================================= *)
(*  Part A — the ζ² ↔ τ dictionary                                    *)
(* ================================================================= *)
Theorem zeta_sq_is_tau : forall n, dconv done done n = dtau n.
Proof. reflexivity. Qed.

Theorem zeta_sq_mult : multiplicative dtau.
Proof. exact dtau_mult. Qed.

Theorem zeta_sq_ppow : forall p k, prime (Z.of_nat p) -> dtau (p ^ k)%nat = Z.of_nat (S k).
Proof. exact tau_ppow. Qed.

Theorem zeta_sq_as_div : forall n, (1 <= n)%nat -> dtau n = Z.of_nat (length (divisors n)).
Proof. exact dtau_as_div. Qed.

(* ================================================================= *)
(*  Part B — |mu| (squarefree indicator) is multiplicative           *)
(* ================================================================= *)
Definition musq (n : nat) : Z := Z.abs (mu n).

Lemma musq_1 : musq 1%nat = 1.
Proof. unfold musq; rewrite mu_1; reflexivity. Qed.

Lemma musq_mult : multiplicative musq.
Proof.
  split; [ exact musq_1 | ].
  intros m n Hm Hn Hg; unfold musq.
  destruct mu_mult as [_ Hmu]; rewrite (Hmu m n Hm Hn Hg), Z.abs_mul; reflexivity.
Qed.

Lemma musq_p : forall p, prime (Z.of_nat p) -> musq p = 1.
Proof. intros p Hp; unfold musq; rewrite (mu_p p Hp); reflexivity. Qed.

Lemma musq_ppow_ge2 : forall p k, prime (Z.of_nat p) -> (2 <= k)%nat -> musq (p ^ k)%nat = 0.
Proof. intros p k Hp Hk; unfold musq; rewrite (mu_ppow_ge2 p k Hp Hk); reflexivity. Qed.

(* ================================================================= *)
(*  Part C — two_om = |mu| ∗ 1, multiplicativity and prime-power value*)
(* ================================================================= *)
Definition two_om : nat -> Z := dconv musq done.

Theorem two_om_mult : multiplicative two_om.
Proof. unfold two_om; apply dconv_mult; [ exact musq_mult | exact done_mult ]. Qed.

Theorem two_om_ppow : forall p k, prime (Z.of_nat p) -> (1 <= k)%nat -> two_om (p ^ k)%nat = 2.
Proof.
  intros p k Hp Hk; unfold two_om.
  rewrite (dconv_as_div musq done (p ^ k) (ppow_pos p k Hp)).
  rewrite (sumf_ext (divisors (p ^ k)) (fun d => musq d * done (p ^ k / d)%nat) musq)
    by (intros d _; unfold done; ring).
  rewrite (divisors_ppow_sum p k musq Hp).
  destruct k as [|k']; [ lia | ].
  replace (seq 0 (S (S k'))) with (0 :: 1 :: seq 2 k')%nat by reflexivity.
  rewrite !sumf_cons'.
  rewrite Nat.pow_0_r, musq_1, Nat.pow_1_r, (musq_p p Hp).
  rewrite (sumf_ext (seq 2 k') (fun j => musq (p ^ j)%nat) (fun _ => 0)).
  - rewrite sumf_zero; ring.
  - intros j Hj; apply in_seq in Hj; apply musq_ppow_ge2; [ exact Hp | lia ].
Qed.

(* ================================================================= *)
(*  Part D — ω(n) and the main identity two_om = 2^ω                  *)
(* ================================================================= *)
Definition primeb (n : nat) : bool :=
  (2 <=? n)%nat && forallb (fun d => negb (n mod d =? 0)%nat) (seq 2 (n - 2)).

Lemma primeb_prime : forall n, primeb n = true <-> prime (Z.of_nat n).
Proof.
  intro n; rewrite <- prime_alt; unfold prime', primeb.
  rewrite Bool.andb_true_iff, Nat.leb_le, forallb_forall; split.
  - intros [Hn2 Hall]; split; [ lia | ].
    intros z Hz.
    set (m := Z.to_nat z).
    assert (Hzm : z = Z.of_nat m) by (unfold m; rewrite Z2Nat.id by lia; reflexivity).
    assert (Hm : (2 <= m < n)%nat) by (rewrite Hzm in Hz; lia).
    intro Hdvd; rewrite Hzm in Hdvd; apply dvd_Z_nat in Hdvd.
    apply Nat.Lcm0.mod_divide in Hdvd.
    assert (Hin : In m (seq 2 (n - 2))) by (apply in_seq; lia).
    pose proof (Hall m Hin) as Hh;
      rewrite Bool.negb_true_iff, Nat.eqb_neq in Hh; contradiction.
  - intros [Hn1 Hno]; split; [ lia | ].
    intros d Hd; apply in_seq in Hd.
    rewrite Bool.negb_true_iff, Nat.eqb_neq; intro Hmod.
    apply Nat.Lcm0.mod_divide, dvd_nat_Z in Hmod.
    apply (Hno (Z.of_nat d)); [ lia | exact Hmod ].
Qed.

Definition omega (n : nat) : nat := length (filter primeb (divisors n)).

Lemma omega_1 : omega 1%nat = 0%nat.
Proof. reflexivity. Qed.

(* x | p with x ≥ 2 and p prime forces x = p *)
Lemma prime_dvd_prime_eq : forall x p, prime (Z.of_nat p) -> (2 <= x)%nat ->
  Nat.divide x p -> x = p.
Proof.
  intros x p Hp Hx Hd.
  assert (Hle : (x <= p)%nat) by (apply Nat.divide_pos_le; [ pose proof (prime_ge_2 _ Hp); lia | exact Hd ]).
  destruct (Nat.eq_dec x p) as [->|Hne]; [ reflexivity | exfalso ].
  apply prime_alt in Hp; destruct Hp as [_ Hno].
  apply (Hno (Z.of_nat x)); [ split; [ lia | apply Nat2Z.inj_lt; lia ] | apply dvd_nat_Z; exact Hd ].
Qed.

Lemma omega_step : forall p v m, prime (Z.of_nat p) -> ~ Nat.divide p m ->
  (1 <= v)%nat -> (1 <= m)%nat -> omega (p ^ v * m)%nat = S (omega m).
Proof.
  intros p v m Hp Hpm Hv Hm.
  assert (Hp2 : (2 <= p)%nat) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hpv : (1 <= p ^ v)%nat) by (apply ppow_pos; exact Hp).
  assert (Hpvm : (1 <= p ^ v * m)%nat) by nia.
  assert (Hpdvd : Nat.divide p (p ^ v * m)).
  { apply (Nat.divide_trans p (p ^ v)%nat); [ | exists m; ring ].
    exists (p ^ (v - 1))%nat; replace v with (S (v - 1)) at 1 by lia; cbn [Nat.pow]; ring. }
  unfold omega.
  assert (Hperm : Permutation (filter primeb (divisors (p ^ v * m)))
                              (p :: filter primeb (divisors m))).
  { apply NoDup_Permutation.
    - apply NoDup_filter, divisors_nodup.
    - constructor.
      + rewrite filter_In; intros [Hin _]; apply in_divisors in Hin.
        apply Hpm; apply Nat.Lcm0.mod_divide; tauto.
      + apply NoDup_filter, divisors_nodup.
    - intro x; rewrite filter_In, in_divisors; split.
      + intros [[Hxr Hxmod] Hxb].
        assert (Hxp : prime (Z.of_nat x)) by (apply primeb_prime; exact Hxb).
        assert (Hx2 : (2 <= x)%nat) by (pose proof (prime_ge_2 _ Hxp); lia).
        assert (Hxd : Nat.divide x (p ^ v * m)) by (apply Nat.Lcm0.mod_divide; tauto).
        destruct (prime_dvd_mult_nat x (p ^ v) m Hxp Hxd) as [Hxpv|Hxm].
        * left; symmetry; apply prime_dvd_prime_eq;
            [ exact Hp | exact Hx2 | apply (prime_dvd_pow x p v Hxp Hxpv) ].
        * right; rewrite filter_In, in_divisors.
          assert (Hxle : (x <= m)%nat) by (apply Nat.divide_pos_le; [ lia | exact Hxm ]).
          repeat split; [ lia | lia | apply Nat.Lcm0.mod_divide; exact Hxm | exact Hxb ].
      + intros [->|Hx].
        * split; [ split; [ split; [ lia | apply Nat.divide_pos_le; [ lia | exact Hpdvd ] ]
                                    | apply Nat.Lcm0.mod_divide; exact Hpdvd ]
                 | apply primeb_prime; exact Hp ].
        * rewrite filter_In, in_divisors in Hx.
          destruct Hx as [[[Hx1 Hxm] Hxmod] Hxb].
          assert (Hxd : Nat.divide x (p ^ v * m)).
          { apply (Nat.divide_trans x m);
              [ apply Nat.Lcm0.mod_divide; exact Hxmod | exists (p ^ v)%nat; ring ]. }
          split; [ split; [ split; [ lia | apply Nat.divide_pos_le; [ lia | exact Hxd ] ]
                                    | apply Nat.Lcm0.mod_divide; exact Hxd ]
                 | exact Hxb ]. }
  rewrite (Permutation_length Hperm); reflexivity.
Qed.

Theorem two_om_eq : forall n, (1 <= n)%nat -> two_om n = Z.of_nat (2 ^ omega n).
Proof.
  apply (mult_ind (fun n => two_om n = Z.of_nat (2 ^ omega n))).
  - vm_compute; reflexivity.
  - intros p v m Hp Hpm Hv Hm IH.
    assert (Hgc : Nat.gcd (p ^ v) m = 1%nat) by (apply gcd_ppow_coprime; assumption).
    assert (Hpv : (1 <= p ^ v)%nat) by (apply ppow_pos; exact Hp).
    destruct two_om_mult as [_ Hmul].
    rewrite (Hmul (p ^ v)%nat m Hpv Hm Hgc), (two_om_ppow p v Hp Hv), IH.
    rewrite (omega_step p v m Hp Hpm Hv Hm).
    replace (2 ^ S (omega m))%nat with (2 * 2 ^ omega m)%nat by (cbn [Nat.pow]; ring).
    rewrite Nat2Z.inj_mul; reflexivity.
Qed.

(* ================================================================= *)
(*  Part E — reflective cross-check and the umbrella                  *)
(* ================================================================= *)
Definition zsq_check (N : nat) : bool :=
  forallb (fun n => two_om n =? Z.of_nat (2 ^ omega n)) (seq 1 N).

Theorem zsq_upto : zsq_check 100 = true.
Proof. vm_compute; reflexivity. Qed.

Theorem zeta_square :
  (* ζ² ↔ τ *)
  (forall n, dconv done done n = dtau n) /\
  multiplicative dtau /\
  (forall p k, prime (Z.of_nat p) -> dtau (p ^ k)%nat = Z.of_nat (S k)) /\
  (forall n, (1 <= n)%nat -> dtau n = Z.of_nat (length (divisors n))) /\
  (* ζ²/ζ(2s) ↔ 2^ω *)
  multiplicative musq /\
  multiplicative two_om /\
  (forall p k, prime (Z.of_nat p) -> (1 <= k)%nat -> two_om (p ^ k)%nat = 2) /\
  (forall n, (1 <= n)%nat -> two_om n = Z.of_nat (2 ^ omega n)) /\
  zsq_check 100 = true.
Proof.
  exact (conj zeta_sq_is_tau
         (conj zeta_sq_mult
         (conj zeta_sq_ppow
         (conj zeta_sq_as_div
         (conj musq_mult
         (conj two_om_mult
         (conj two_om_ppow
         (conj two_om_eq
               zsq_upto)))))))).
Qed.

Print Assumptions zeta_square.

(* ================================================================= *)
(*  END DirichletZetaSquare.v                                        *)
(*  ζ(s)² ↔ τ made explicit, and ζ(s)²/ζ(2s) ↔ 2^ω(n) proven         *)
(*  ((|mu|∗1)(n) = #squarefree divisors = 2^ω).  Closed under the     *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
