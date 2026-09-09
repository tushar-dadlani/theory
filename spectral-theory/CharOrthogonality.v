(* ================================================================= *)
(*  CharOrthogonality.v  --  orthogonality in the CHARACTER variable. *)
(*                                                                    *)
(*    sum_{a=0}^{p-2} chi_a(n)  =  (p-1) if n = 1 mod p, else 0       *)
(*                                                                    *)
(*  GaussSum.char_sum_zero is the sum over n at fixed character (which *)
(*  is what CCharSumBound and the whole continuation rest on).  This   *)
(*  is the DUAL: the sum over characters at fixed n.  It is the        *)
(*  selector that isolates one residue class, and it is the second of  *)
(*  the two inputs Dirichlet's theorem needs (the other being          *)
(*  L(1,chi) <> 0, now in LFunOne).                                    *)
(*                                                                    *)
(*  Almost nothing new is required: dchar p g a n is                   *)
(*  (w (p-1))^(a * dlog n), so summing over a is literally the DFT     *)
(*  orthogonality RootsOfUnity.dft_orthogonality_delta at j = dlog n.  *)
(*  The only content is that dlog n = 0 exactly when n = 1 mod p,      *)
(*  which is dlog_pow one way and dlog_inv the other.                  *)
(*                                                                    *)
(*  The paired form sums chi_a(n) chi_a(m) and selects n m = 1 mod p;  *)
(*  taking m to be the inverse of a target residue r turns it into the *)
(*  indicator of n = r, which is how it gets used.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Znumtheory List.
Require Import ComplexField Cmodulus RootsOfUnity ZmodOrder DirichletModP
        DirichletLEuler.
Open Scope R_scope.

Lemma Csum_C0 : forall N, Csum (fun _ => C0) N = C0.
Proof.
  induction N as [| N IH]; [ reflexivity | ].
  cbn [Csum]. rewrite IH. apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring.
Qed.

Theorem char_orthogonality : forall p g n,
  prime (Z.of_nat p) -> (1 <= g <= p - 1)%nat -> ord p g = (p - 1)%nat ->
  Csum (fun a => dchar p g a n) (p - 1)
  = (if (n mod p =? 1)%nat then RtoC (INR (p - 1)) else C0).
Proof.
  intros p g n Hp Hg Hord.
  assert (Hp2 : (2 <= p)%nat) by (pose proof (prime_ge_2 _ Hp); lia).
  assert (Hpw0 : pw p g 0 = 1%nat)
    by (unfold pw; cbn [Nat.pow]; apply Nat.mod_small; lia).
  destruct (n mod p =? 0)%nat eqn:E0.
  - assert (Hne1 : (n mod p =? 1)%nat = false)
      by (apply Nat.eqb_eq in E0; apply Nat.eqb_neq; lia).
    rewrite Hne1.
    rewrite (Csum_ext (fun a => dchar p g a n) (fun _ => C0) (p - 1)).
    + apply Csum_C0.
    + intro a. unfold dchar. rewrite E0. reflexivity.
  - assert (Hj : (dlog p g (n mod p) < p - 1)%nat) by (apply dlog_lt; lia).
    rewrite (Csum_ext (fun a => dchar p g a n)
               (fun a => Cpow (Cpow (w (p - 1)) (dlog p g (n mod p))) a) (p - 1)).
    2: { intro a. unfold dchar. rewrite E0.
         rewrite <- Cpow_mul. f_equal. lia. }
    rewrite (dft_orthogonality_delta (p - 1) (dlog p g (n mod p)) Hj).
    assert (Hiff : (dlog p g (n mod p) =? 0)%nat = (n mod p =? 1)%nat).
    { destruct (n mod p =? 1)%nat eqn:E1.
      - apply Nat.eqb_eq in E1. apply Nat.eqb_eq. rewrite E1, <- Hpw0.
        apply dlog_pow; [ exact Hp | exact Hg | exact Hord | lia ].
      - apply Nat.eqb_neq in E1. apply Nat.eqb_neq. intro Hj0. apply E1.
        assert (Hm : (1 <= n mod p <= p - 1)%nat).
        { apply Nat.eqb_neq in E0.
          pose proof (Nat.mod_upper_bound n p ltac:(lia)). lia. }
        pose proof (dlog_inv p g (n mod p) Hp Hg Hord Hm) as Hinv.
        rewrite Hj0, Hpw0 in Hinv. lia. }
    rewrite Hiff. reflexivity.
Qed.

(* the form that isolates a residue class *)
Corollary char_orthogonality_pair : forall p g n m,
  prime (Z.of_nat p) -> (1 <= g <= p - 1)%nat -> ord p g = (p - 1)%nat ->
  Csum (fun a => Cmul (dchar p g a n) (dchar p g a m)) (p - 1)
  = (if ((n * m) mod p =? 1)%nat then RtoC (INR (p - 1)) else C0).
Proof.
  intros p g n m Hp Hg Hord.
  rewrite <- (char_orthogonality p g (n * m) Hp Hg Hord).
  apply Csum_ext. intro a. symmetry. apply (dchar_mul p g a n m Hp Hg Hord).
Qed.

Print Assumptions char_orthogonality.
Print Assumptions char_orthogonality_pair.

(* ================================================================= *)
(*  END CharOrthogonality.v                                           *)
(* ================================================================= *)
