(* ================================================================= *)
(*  LFunOne.v  --  transporting the real-character result onto LFun,  *)
(*  and closing the case split.                                       *)
(*                                                                    *)
(*  HyperbolaUpper.Lchi1_ne0 is about Lchi1, a REAL number defined as  *)
(*  the limit of its own series.  CLHolo1.LFun is the holomorphic      *)
(*  continuation, a C -> C function defined by proj1_sig.  They have   *)
(*  to be identified before the two halves of the case split can meet. *)
(*                                                                    *)
(*    LFun_at_one : LFun p g A ... C1 = RtoC (Lchi1 p g A ...)        *)
(*                                                                    *)
(*  and then, since CLLineNonzero.LFun_one_nonzero assumes             *)
(*  0 < (2A) mod (p-1) < p-1 -- exactly chi^2 <> chi_0 -- while the    *)
(*  hyperbola handles chi real, the two cover everything:              *)
(*                                                                    *)
(*    LFun_one_nonzero_all : L(1,chi) <> 0 for EVERY non-principal chi *)
(*                                                                    *)
(*  The bridge in the degenerate direction is chi^2 = chi_0 ==> chi    *)
(*  real: z*z = 1 forces Im z = 0, because (a,b)^2 = (a^2-b^2, 2ab)    *)
(*  and b <> 0 would give a = 0 and -b^2 = 1.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Znumtheory
     FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CSeries RootsOfUnity ZmodOrder
        DirichletModP CZetaRegular3 CTwistedCoeff CLSeries CLHolo1
        CTwistPerPrime CLLineTools CLLineNonzero
        CRealChar CharTailBound HyperbolaUpper.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- real sequences inside the complex series machinery.      *)
(* ----------------------------------------------------------------- *)

Lemma Cpsum_RtoC : forall (b : nat -> R) N,
  Cpsum (fun n => RtoC (b n)) N = RtoC (sum_f_R0 b N).
Proof.
  intros b N. induction N as [| N IH]; [ reflexivity | ].
  replace (Cpsum (fun n => RtoC (b n)) (S N))
    with (Cadd (Cpsum (fun n => RtoC (b n)) N) (RtoC (b (S N)))) by reflexivity.
  rewrite IH, tech5. apply Ceq; unfold Cadd, RtoC; cbn [Re Im]; ring.
Qed.

Lemma CUn_cv_RtoC : forall (u : nat -> R) L,
  Un_cv u L -> CUn_cv (fun N => RtoC (u N)) (RtoC L).
Proof.
  intros u L H eps He. destruct (H eps He) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in HN.
  replace (Cminus (RtoC (u n)) (RtoC L)) with (RtoC (u n - L))
    by (apply Ceq; unfold Cminus, Cadd, Copp, RtoC; cbn [Re Im]; ring).
  rewrite Cmod_RtoC. exact HN.
Qed.

Lemma RtoC_eq0 : forall x : R, RtoC x = C0 -> x = 0.
Proof.
  intros x H. apply (f_equal Re) in H. unfold RtoC, C0 in H. cbn [Re] in H. exact H.
Qed.

(* z*z = 1 forces z real *)
Lemma Csq_one_real : forall z : C, Cmul z z = C1 -> Cconj z = z.
Proof.
  intros z H.
  assert (HR : Re z * Re z - Im z * Im z = 1).
  { apply (f_equal Re) in H. unfold Cmul, C1 in H. cbn [Re Im] in H. lra. }
  assert (HI : Re z * Im z + Im z * Re z = 0).
  { apply (f_equal Im) in H. unfold Cmul, C1 in H. cbn [Re Im] in H. lra. }
  assert (Hb : Im z = 0).
  { destruct (Req_dec (Im z) 0) as [E | E]; [ exact E | ].
    exfalso. assert (Re z = 0) by nra. nra. }
  apply Ceq; unfold Cconj; cbn [Re Im]; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- LFun at s = 1 for a real character.                      *)
(* ----------------------------------------------------------------- *)

Section AtOne.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.
Hypothesis Hreal : forall n, Cconj (dchar p g A n) = dchar p g A n.

Lemma Lterm_at_one : forall n, Lterm p g A C1 n = RtoC (ca p g A n * w1 n).
Proof.
  intro n. unfold Lterm, Gchi.
  rewrite (Cpw_negC1 (INR (S n)))
    by (apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); lia ]).
  rewrite <- (chz_spec p g A Hreal (S n)).
  unfold ca, cr, w1. apply Ceq; unfold Cmul, RtoC; cbn [Re Im]; ring.
Qed.

Theorem LFun_at_one :
  LFun p g A Hp Hg Hord HA C1 = RtoC (Lchi1 p g A Hp Hg Hord HA Hreal).
Proof.
  symmetry. apply LFun_unique; [ unfold C1; cbn [Re]; lra | ].
  unfold Cseries_cv.
  replace (Lterm p g A C1) with (fun n => RtoC (ca p g A n * w1 n))
    by (apply functional_extensionality; intro n; symmetry; apply Lterm_at_one).
  replace (Cpsum (fun n => RtoC (ca p g A n * w1 n)))
    with (fun N => RtoC (sum_f_R0 (fun k => ca p g A k * w1 k) N))
    by (apply functional_extensionality; intro N; symmetry; apply Cpsum_RtoC).
  apply CUn_cv_RtoC. apply Lchi1_cv.
Qed.

Theorem LFun_one_nonzero_real : LFun p g A Hp Hg Hord HA (mkC 1 0) <> C0.
Proof.
  change (mkC 1 0) with C1. rewrite LFun_at_one. intro Hc.
  apply (Lchi1_ne0 p g A Hp Hg Hord HA Hreal). apply RtoC_eq0. exact Hc.
Qed.

End AtOne.

(* ----------------------------------------------------------------- *)
(*  Part C -- the case split closes.                                   *)
(* ----------------------------------------------------------------- *)

Section AllChars.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.

(* the degenerate branch really is the real branch *)
Lemma degenerate_is_real : ((2 * A) mod (p - 1) = 0)%nat ->
  forall n, Cconj (dchar p g A n) = dchar p g A n.
Proof.
  intros Hdeg n.
  assert (Hp1 : (0 < p - 1)%nat) by lia.
  destruct (Nat.eqb (n mod p) 0) eqn:E.
  - assert (Hd : Nat.divide p n)
      by (apply (proj1 (Nat.Lcm0.mod_divide n p)); apply Nat.eqb_eq; exact E).
    rewrite (dchar_zero p g A n Hd). apply Ceq; unfold Cconj, C0; cbn [Re Im]; ring.
  - apply Csq_one_real.
    rewrite (dchar_index_add p g A A n).
    replace (A + A)%nat with (2 * A)%nat by lia.
    rewrite (dchar_index_mod p g (2 * A) n Hp1), Hdeg.
    unfold dchar. rewrite E. rewrite Nat.mul_0_l. reflexivity.
Qed.

Theorem LFun_one_nonzero_all : LFun p g A Hp Hg Hord HA (mkC 1 0) <> C0.
Proof.
  destruct (Nat.eq_dec ((2 * A) mod (p - 1)) 0) as [Hdeg | Hdeg].
  - apply (LFun_one_nonzero_real p g A Hp Hg Hord HA (degenerate_is_real Hdeg)).
  - apply (LFun_one_nonzero p g A Hp Hg Hord HA).
    assert (Hlt : ((2 * A) mod (p - 1) < p - 1)%nat)
      by (apply Nat.mod_upper_bound; lia).
    lia.
Qed.

End AllChars.

Print Assumptions LFun_one_nonzero_all.

(* ================================================================= *)
(*  END LFunOne.v                                                     *)
(* ================================================================= *)
