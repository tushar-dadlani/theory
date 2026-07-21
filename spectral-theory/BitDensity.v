(* ================================================================= *)
(*  BitDensity.v                                                      *)
(*                                                                    *)
(*  THE BIT DENSITY OF STATES AND ITS SYMMETRY ABOUT 1/2.             *)
(*                                                                    *)
(*  On the n-bit cube F_2^n a "state" is a Walsh mode; its ENERGY is  *)
(*  the number of flipped bits (its Hamming weight), and the number   *)
(*  of states at energy k is the binomial C(n,k) -- the DENSITY OF    *)
(*  STATES (bit density).  On F_2^3 this is the row 1,3,3,1, matching  *)
(*  the multiplicities implicit in MassGap.v's `excite`.              *)
(*                                                                    *)
(*  We prove (pure nat combinatorics, axiom-free):                    *)
(*    - dos_symmetric : the density is symmetric under the COMPLEMENT  *)
(*      involution k -> n-k (flip every bit), i.e. C(n,k) = C(n,n-k);  *)
(*    - the complement is an involution whose fixed point is k = n/2;  *)
(*    - cube3_dos : the 3-bit density is [1;3;3;1], summing to 2^3.    *)
(*                                                                    *)
(*  HONEST SCOPE / relation to zeta zeros.  This is an ANALOGY, not a  *)
(*  theorem about the Riemann zeta zeros -- the repo contains no       *)
(*  actual zeta function and no zero-counting/density.  The genuine    *)
(*  parallel is the shared symmetry: the bit density is organised by   *)
(*  the complement involution k -> n-k about its fixed point n/2, the  *)
(*  same shape as zeta's functional-equation involution s -> 1-s about *)
(*  1/2 (present here only as the toy `spectral_involution` and the    *)
(*  `s = 1-s -> s = 1/2` lemma).  It is NOT a statement about the      *)
(*  zeros' counting law (Riemann-von Mangoldt N(T) ~ (T/2π)ln(T/2π),   *)
(*  growing like T log T) or their GUE spacing -- neither is in the    *)
(*  repo, and both differ in kind from this finite binomial density.   *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* SECTION 1 — binomial coefficients (Pascal), the density of states  *)
(* ----------------------------------------------------------------- *)

Fixpoint binomial (n k : nat) : nat :=
  match n with
  | 0    => match k with 0 => 1 | S _ => 0 end
  | S n' => match k with
            | 0    => 1
            | S k' => binomial n' k' + binomial n' (S k')
            end
  end.

(* the bit density of states: number of n-bit states of energy k *)
Definition dos (n k : nat) : nat := binomial n k.

Lemma binom_0_r : forall n, binomial n 0 = 1.
Proof. intro n; destruct n; reflexivity. Qed.

(* above the top there are no states *)
Lemma binom_gt : forall n k, n < k -> binomial n k = 0.
Proof.
  induction n as [|n IH]; intros k Hk.
  - destruct k; [ lia | reflexivity ].
  - destruct k as [|k]; [ lia | ].
    simpl; rewrite (IH k), (IH (S k)) by lia; reflexivity.
Qed.

(* the top state is unique *)
Lemma binom_diag : forall n, binomial n n = 1.
Proof.
  induction n as [|n IH]; [ reflexivity | ].
  simpl; rewrite IH, (binom_gt n (S n)) by lia; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — symmetry under the complement involution k -> n-k     *)
(* ----------------------------------------------------------------- *)

(* THE HEADLINE: the density of states is symmetric about the midpoint *)
(* -- C(n,k) = C(n,n-k) -- the discrete analogue of s -> 1-s. *)
Theorem dos_symmetric : forall n k, k <= n -> dos n k = dos n (n - k).
Proof.
  unfold dos; induction n as [|n IH]; intros k Hk.
  - assert (k = 0) by lia; subst; reflexivity.
  - destruct k as [|k'].
    + rewrite binom_0_r, Nat.sub_0_r, binom_diag; reflexivity.
    + destruct (Nat.eq_dec (S k') (S n)) as [Heq | Hne].
      * rewrite Heq, Nat.sub_diag, binom_diag, binom_0_r; reflexivity.
      * replace (S n - S k') with (S (n - S k')) by lia.
        cbn [binomial].
        rewrite (IH k') by lia.
        rewrite (IH (S k')) by lia.
        replace (n - k') with (S (n - S k')) by lia.
        lia.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — the complement is an involution with fixed point n/2  *)
(* ----------------------------------------------------------------- *)

(* flipping all bits twice is the identity *)
Theorem complement_involutive : forall n k, k <= n -> n - (n - k) = k.
Proof. intros; lia. Qed.

(* its unique fixed point is the half-weight n/2 (the "critical line") *)
Theorem complement_fixed_iff : forall n k,
  k <= n -> (n - k = k <-> n = 2 * k).
Proof. intros; lia. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 4 — the 3-bit cube: density [1;3;3;1] summing to 2^3       *)
(* ----------------------------------------------------------------- *)

Theorem cube3_dos : map (dos 3) [0; 1; 2; 3] = [1; 3; 3; 1].
Proof. vm_compute; reflexivity. Qed.

Theorem cube3_total : dos 3 0 + dos 3 1 + dos 3 2 + dos 3 3 = 2 ^ 3.
Proof. vm_compute; reflexivity. Qed.

(* the density peaks at the centre (the fixed point k = 3/2 lies       *)
(* between the two maxima k=1,2), symmetric under k -> 3-k.            *)
Theorem cube3_peak : dos 3 0 <= dos 3 1 /\ dos 3 2 >= dos 3 3.
Proof. vm_compute; lia. Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM                                                     *)
(* ----------------------------------------------------------------- *)

Theorem bit_density_symmetric_about_half :
  (* the bit density is symmetric under the complement involution ... *)
  (forall n k, k <= n -> dos n k = dos n (n - k))
  (* ... which is an involution ... *)
  /\ (forall n k, k <= n -> n - (n - k) = k)
  (* ... whose fixed point is the half-weight n/2 (the critical line) *)
  /\ (forall n k, k <= n -> (n - k = k <-> n = 2 * k))
  (* ... and on the 3-bit cube the density is the binomial row 1,3,3,1 *)
  /\ map (dos 3) [0; 1; 2; 3] = [1; 3; 3; 1].
Proof.
  split; [ exact dos_symmetric | ].
  split; [ exact complement_involutive | ].
  split; [ exact complement_fixed_iff | exact cube3_dos ].
Qed.

Print Assumptions bit_density_symmetric_about_half.

(* ================================================================= *)
(*  END BitDensity.v                                                  *)
(*  The bit density of states is symmetric under the complement       *)
(*  involution about the half-weight n/2 -- the discrete shadow of     *)
(*  the critical line at 1/2.  A real theorem; an honest analogy.      *)
(*  ZERO Admitted; no axioms.                                         *)
(* ================================================================= *)
