(* ================================================================= *)
(*  CZetaRegular.v   (Phase B: the regular part of zeta at s=1)         *)
(*                                                                    *)
(*  The continued zeta is  zetaC s = 1/(s-1) + g(s),  g = sum gtermC,   *)
(*  where each gtermC carries a 1/(1-s) (singular per-term at s=1).     *)
(*  Multiplying by (s-1) CLEARS that division:                         *)
(*                                                                    *)
(*    bterm s n := (s-1)(n+1)^{-s} + (n+2)^{1-s} - (n+1)^{1-s}          *)
(*              =  (s-1) * gtermC s n           (for s <> 1)            *)
(*                                                                    *)
(*  Each bterm is ENTIRE (a combination of Cpw's, no Cinv), so the sum  *)
(*    Bfn s := 1 + sum_n bterm s n   ( = (s-1)*zetaC s  for s<>1 )      *)
(*  is the REGULAR part: holomorphic on {Re>0} INCLUDING s=1, value 1.  *)
(*                                                                    *)
(*  This file: bterm, its manifest holomorphy, the value identity      *)
(*  bterm = (s-1) gtermC off 1, convergence of the sum, and Bfn with    *)
(*  Bfn_eq / Bfn_at1.  (Holomorphy of Bfn ACROSS s=1 is CZetaRegular2.) *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CexpFull EulerFormula CPower
        CSeries CSeriesLin CZetaTerm.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Cpw with a complex-affine exponent is holomorphic (base > 0)      *)
(* ----------------------------------------------------------------- *)
Lemma cpw_neg_holo : forall (c : R), 0 < c -> forall s,
  is_Cderiv (fun w => Cpw c (Copp w)) s
            (Cmul (Copp C1) (Cmul (RtoC (ln c)) (Cpw c (Copp s)))).
Proof.
  intros c Hc s.
  apply (is_Cderiv_ext (fun w => Cpw c (Cadd (Cmul (Copp C1) w) C0))
                       (fun w => Cpw c (Copp w))).
  - intro w. f_equal. apply Ceq; unfold Cadd, Cmul, Copp, C0, C1; cbn [Re Im]; ring.
  - replace (Cmul (Copp C1) (Cmul (RtoC (ln c)) (Cpw c (Copp s))))
       with (Cmul (Copp C1) (Cmul (RtoC (ln c)) (Cpw c (Cadd (Cmul (Copp C1) s) C0)))).
    + apply (Cderiv_comp_affine (fun v => Cpw c v) (Copp C1) C0 s).
      apply Cpw_deriv; exact Hc.
    + f_equal. f_equal. f_equal. apply Ceq; unfold Cadd, Cmul, Copp, C0, C1; cbn [Re Im]; ring.
Qed.

Lemma cpw_1minus_holo : forall (c : R), 0 < c -> forall s,
  is_Cderiv (fun w => Cpw c (Cminus C1 w)) s
            (Cmul (Copp C1) (Cmul (RtoC (ln c)) (Cpw c (Cminus C1 s)))).
Proof.
  intros c Hc s.
  apply (is_Cderiv_ext (fun w => Cpw c (Cadd (Cmul (Copp C1) w) C1))
                       (fun w => Cpw c (Cminus C1 w))).
  - intro w. f_equal. apply Ceq; unfold Cadd, Cmul, Copp, C1, Cminus; cbn [Re Im]; ring.
  - replace (Cmul (Copp C1) (Cmul (RtoC (ln c)) (Cpw c (Cminus C1 s))))
       with (Cmul (Copp C1) (Cmul (RtoC (ln c)) (Cpw c (Cadd (Cmul (Copp C1) s) C1)))).
    + apply (Cderiv_comp_affine (fun v => Cpw c v) (Copp C1) C1 s).
      apply Cpw_deriv; exact Hc.
    + f_equal. f_equal. f_equal. apply Ceq; unfold Cadd, Cmul, Copp, C1, Cminus; cbn [Re Im]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the regular term  bterm  and its manifest holomorphy              *)
(* ----------------------------------------------------------------- *)
Definition bterm (s : C) (n : nat) : C :=
  Cadd (Cmul (Cminus s C1) (Cpw (INR (S n)) (Copp s)))
       (Cminus (Cpw (INR (S (S n))) (Cminus C1 s))
               (Cpw (INR (S n)) (Cminus C1 s))).

Lemma INR_S_pos : forall n, 0 < INR (S n).
Proof. intro n. apply lt_0_INR; lia. Qed.

Lemma bterm_holo : forall n s, exists d, is_Cderiv (fun w => bterm w n) s d.
Proof.
  intros n s. unfold bterm.
  eexists.
  apply (Cderiv_add
           (fun w => Cmul (Cminus w C1) (Cpw (INR (S n)) (Copp w)))
           (fun w => Cminus (Cpw (INR (S (S n))) (Cminus C1 w))
                            (Cpw (INR (S n)) (Cminus C1 w)))).
  - apply (Cderiv_mul (fun w => Cminus w C1) (fun w => Cpw (INR (S n)) (Copp w))).
    + apply (Cderiv_minus (fun w => w) (fun _ => C1)); [ apply Cderiv_id | apply Cderiv_const ].
    + apply cpw_neg_holo; apply INR_S_pos.
  - apply (Cderiv_minus (fun w => Cpw (INR (S (S n))) (Cminus C1 w))
                        (fun w => Cpw (INR (S n)) (Cminus C1 w)));
      apply cpw_1minus_holo; apply INR_S_pos.
Qed.

(* ----------------------------------------------------------------- *)
(*  bterm = (s-1) * gtermC  off the pole                              *)
(* ----------------------------------------------------------------- *)
Lemma bterm_eq : forall s n, Cminus C1 s <> C0 ->
  bterm s n = Cmul (Cminus s C1) (gtermC s n).
Proof.
  intros s n H1. unfold bterm, gtermC, gC, GC.
  field. exact H1.
Qed.

(* ----------------------------------------------------------------- *)
(*  Cpw with a zero exponent is 1  (for the s=1 evaluation)           *)
(* ----------------------------------------------------------------- *)
Lemma Cpw_C0 : forall c, Cpw c C0 = C1.
Proof.
  intro c; unfold Cpw.
  replace (Cmul C0 (RtoC (ln c))) with C0 by ring.
  unfold Cexpf, C0; cbn [Re Im].
  rewrite exp_0, Cexp_0.
  unfold RtoC, C1, Cmul; apply Ceq; cbn; ring.
Qed.

(* bterm at s=1 is 0 (each summand vanishes) *)
Lemma bterm_at1 : forall n, bterm C1 n = C0.
Proof.
  intro n. unfold bterm.
  replace (Cminus C1 C1) with C0 by (apply Ceq; unfold Cminus, Cadd, Copp, C0, C1; cbn [Re Im]; ring).
  rewrite !Cpw_C0.
  apply Ceq; unfold Cadd, Cmul, Cminus, Copp, C0, C1; cbn [Re Im]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  convergence of  sum_n bterm s n  on Re s > 0                      *)
(* ----------------------------------------------------------------- *)
Lemma Cseries_cv_ext : forall (a b : nat -> C) S,
  (forall n, a n = b n) -> Cseries_cv a S -> Cseries_cv b S.
Proof.
  intros a b S Hab Ha.
  replace b with a by (apply functional_extensionality; exact Hab). exact Ha.
Qed.

Definition Ceq_dec (a b : C) : {a = b} + {a <> b}.
Proof.
  destruct (Req_EM_T (Re a) (Re b)) as [HR | HR];
  destruct (Req_EM_T (Im a) (Im b)) as [HI | HI].
  - left; apply Ceq; assumption.
  - right; intro E; subst; apply HI; reflexivity.
  - right; intro E; subst; apply HR; reflexivity.
  - right; intro E; subst; apply HR; reflexivity.
Defined.

Lemma bterm_cv : forall s, 0 < Re s -> { B | Cseries_cv (bterm s) B }.
Proof.
  intros s Hs.
  destruct (Ceq_dec (Cminus C1 s) C0) as [Hpole | Hpole].
  - (* s = 1 : bterm is identically 0 *)
    assert (Hs1 : s = C1).
    { apply Ceq.
      - apply (f_equal Re) in Hpole; unfold Cminus, Cadd, Copp, C0, C1 in Hpole;
        cbn [Re Im] in Hpole; unfold C1; cbn [Re]; lra.
      - apply (f_equal Im) in Hpole; unfold Cminus, Cadd, Copp, C0, C1 in Hpole;
        cbn [Re Im] in Hpole; unfold C1; cbn [Im]; lra. }
    exists C0. apply (Cseries_cv_ext (fun _ => C0)).
    + intro n. rewrite Hs1. symmetry; apply bterm_at1.
    + (* series of zeros converges to 0 *)
      unfold Cseries_cv, CUn_cv. intros eps Heps. exists 0%nat. intros n _.
      assert (HC : Cpsum (fun _ : nat => C0) n = C0).
      { clear. induction n as [| k IH]; [ reflexivity | ].
        cbn [Cpsum]. rewrite IH. apply Ceq; unfold Cadd, C0; cbn [Re Im]; ring. }
      rewrite HC.
      assert (Hcm : Cmod (Cminus C0 C0) = 0).
      { apply (proj2 (Cmod0 (Cminus C0 C0))).
        apply Ceq; unfold Cminus, Cadd, Copp, C0; cbn [Re Im]; ring. }
      rewrite Hcm. exact Heps.
  - (* s <> 1 : bterm = (s-1) gtermC, reuse gtermC_cv + cscal *)
    destruct (gtermC_cv s Hs Hpole) as [G HG].
    exists (Cmul (Cminus s C1) G).
    apply (Cseries_cv_ext (fun n => Cmul (Cminus s C1) (gtermC s n))).
    + intro n. symmetry; apply bterm_eq; exact Hpole.
    + apply Cseries_cv_cscal; exact HG.
Qed.

(* ----------------------------------------------------------------- *)
(*  the regular function  Bfn = 1 + sum bterm                        *)
(* ----------------------------------------------------------------- *)
Definition Bsum (s : C) (Hs : 0 < Re s) : C := proj1_sig (bterm_cv s Hs).

Definition Bfn (s : C) (Hs : 0 < Re s) : C := Cadd C1 (Bsum s Hs).

Lemma Bsum_series : forall s (Hs : 0 < Re s), Cseries_cv (bterm s) (Bsum s Hs).
Proof. intros s Hs. unfold Bsum. exact (proj2_sig (bterm_cv s Hs)). Qed.

Print Assumptions bterm_holo.
Print Assumptions bterm_cv.
