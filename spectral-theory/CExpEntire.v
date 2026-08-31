(* CExpEntire.v -- the entire function E(u) = (e^u - 1)/u, with E(0) = 1.

   This is the regularising factor that removes the s = 1 pole from the
   ENCODED zeta terms.  CZetaTerm.GC carries x^(1-s)/(1-s), so every
   gtermC is singular at s = 1 in the encoding, and ZetaFn.zF is defined
   to be C0 there -- the wrong VALUE, not merely a missing derivative.
   Writing the difference of two such powers as

       (b^w - a^w)/w  =  a^w * ln(b/a) * E(w * ln(b/a)),      w = 1 - s

   makes every factor entire.  E is entire precisely because of the
   second-order remainder bound CExpQuot.Cexpf_remainder2. *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus EulerFormula CexpFull CexpfDeriv
        CexpRemainder CExpQuot Holomorphic CDeriv CHoloCalculus CCutoff.
Open Scope R_scope.

(* ---- decidable equality on C, to define E by a guard ---- *)

Definition Ceq_dc (a b : C) : {a = b} + {a <> b}.
Proof.
  destruct (Req_EM_T (Re a) (Re b)) as [H1|H1];
  destruct (Req_EM_T (Im a) (Im b)) as [H2|H2].
  - left; apply Ceq; assumption.
  - right; intro E; apply H2; rewrite E; reflexivity.
  - right; intro E; apply H1; rewrite E; reflexivity.
  - right; intro E; apply H1; rewrite E; reflexivity.
Defined.

Lemma Cmod_pos' : forall c, c <> C0 -> 0 < Cmod c.
Proof.
  intros c Hc. destruct (Rle_lt_or_eq_dec 0 (Cmod c) (Cmod_nonneg c)) as [H|H].
  - exact H.
  - exfalso. apply Hc. apply (proj1 (Cmod0 c)). symmetry; exact H.
Qed.

Lemma Cexpf_at0 : Cexpf C0 = C1.
Proof.
  unfold Cexpf, Cexp, C0, C1; simpl.
  rewrite exp_0, cos_0, sin_0. apply Ceq; simpl; ring.
Qed.

(* ---- the function ---- *)

Definition Eexp (u : C) : C :=
  match Ceq_dc u C0 with
  | left _ => C1
  | right _ => Cmul (Cminus (Cexpf u) C1) (Cinv u)
  end.

Lemma Eexp_at0 : Eexp C0 = C1.
Proof.
  unfold Eexp. destruct (Ceq_dc C0 C0) as [H|H].
  - reflexivity.
  - exfalso; apply H; reflexivity.
Qed.

Lemma Eexp_ne0 : forall u, u <> C0 ->
  Eexp u = Cmul (Cminus (Cexpf u) C1) (Cinv u).
Proof.
  intros u Hu. unfold Eexp. destruct (Ceq_dc u C0) as [H|H].
  - exfalso; apply Hu; exact H.
  - reflexivity.
Qed.

(* The clean characterisation, valid at 0 as well: u * E(u) = e^u - 1. *)
Lemma Eexp_spec : forall u, Cmul (Eexp u) u = Cminus (Cexpf u) C1.
Proof.
  intro u. destruct (Ceq_dc u C0) as [H|H].
  - subst u. rewrite Eexp_at0, Cexpf_at0. ring.
  - rewrite (Eexp_ne0 u H). field. exact H.
Qed.

(* ---- derivative away from 0: quotient rule ---- *)

Lemma Eexp_deriv_ne0 : forall u, u <> C0 -> exists d, is_Cderiv Eexp u d.
Proof.
  intros u Hu.
  eexists.
  apply (is_Cderiv_ext_local Eexp
           (fun w => Cmul (Cminus (Cexpf w) C1) (Cinv w)) u _ (Cmod u)).
  - apply Cmod_pos'; exact Hu.
  - intros w Hw. apply Eexp_ne0.
    intro E. subst w. apply (Rlt_irrefl (Cmod u)).
    replace (Cmod u) with (Cmod (Cminus C0 u)) at 1; [ exact Hw | ].
    replace (Cminus C0 u) with (Copp u) by ring. apply Cmod_opp.
  - apply (Cderiv_div (fun w => Cminus (Cexpf w) C1) (fun w => w) u
             (Cminus (Cexpf u) C0) C1).
    + apply Cderiv_minus; [ apply Cexpf_deriv | apply Cderiv_const ].
    + apply Cderiv_id.
    + exact Hu.
Qed.

(* ---- derivative at 0: E'(0) = 1/2, from the second-order remainder ---- *)

Theorem Eexp_deriv_at0 : is_Cderiv Eexp C0 (RtoC (/ 2)).
Proof.
  intros eps Heps.
  assert (He1 : 0 < exp 1) by apply exp_pos.
  set (del := Rmin 1 (eps / (6 * exp 1))).
  assert (Hdel : 0 < del).
  { apply Rmin_glb_lt; [ lra | ].
    apply Rdiv_lt_0_compat; lra. }
  exists del. split; [ exact Hdel | ].
  intros h Hh.
  replace (Cadd C0 h) with h by ring.
  rewrite Eexp_at0.
  destruct (Ceq_dc h C0) as [Hz|Hz].
  - subst h. rewrite Eexp_at0.
    replace (Cminus (Cminus C1 C1) (Cmul (RtoC (/ 2)) C0)) with C0 by ring.
    rewrite Cmod_C0. lra.
  - (* h <> 0 : divide the second-order remainder by h *)
    assert (Hm : 0 < Cmod h) by (apply Cmod_pos'; exact Hz).
    rewrite (Eexp_ne0 h Hz).
    replace (Cminus (Cminus (Cmul (Cminus (Cexpf h) C1) (Cinv h)) C1)
                    (Cmul (RtoC (/ 2)) h))
      with (Cmul (Cminus (Cminus (Cminus (Cexpf h) C1) h)
                    (Cmul (RtoC (/ 2)) (Cmul h h))) (Cinv h))
      by (field; exact Hz).
    rewrite Cmod_mul, (Cmod_inv h Hz).
    (* now: N / |h| <= eps * |h|, where N <= 6 |h|^3 exp |h| *)
    apply Rle_trans with (6 * Cmod h ^ 3 * exp (Cmod h) * / Cmod h).
    { apply Rmult_le_compat_r.
      - left; apply Rinv_0_lt_compat; exact Hm.
      - apply Cexpf_remainder2. }
    (* 6 |h|^3 e^{|h|} / |h| = 6 |h|^2 e^{|h|} <= eps |h| *)
    replace (6 * Cmod h ^ 3 * exp (Cmod h) * / Cmod h)
      with ((6 * Cmod h * exp (Cmod h)) * Cmod h)
      by (field; lra).
    apply Rmult_le_compat_r; [ lra | ].
    (* 6 |h| e^{|h|} <= eps *)
    assert (Hh1 : Cmod h <= 1).
    { apply Rle_trans with del; [ left; exact Hh | apply Rmin_l ]. }
    assert (Hh2 : Cmod h <= eps / (6 * exp 1)).
    { apply Rle_trans with del; [ left; exact Hh | apply Rmin_r ]. }
    assert (Hex : exp (Cmod h) <= exp 1) by (apply exp_mono_le; exact Hh1).
    apply Rle_trans with (6 * (eps / (6 * exp 1)) * exp 1).
    + apply Rmult_le_compat.
      * lra.
      * left; apply exp_pos.
      * lra.
      * exact Hex.
    + field_simplify; lra.
Qed.

Theorem Eexp_entire : forall u, exists d, is_Cderiv Eexp u d.
Proof.
  intro u. destruct (Ceq_dc u C0) as [H|H].
  - subst u. exists (RtoC (/ 2)). exact Eexp_deriv_at0.
  - apply Eexp_deriv_ne0; exact H.
Qed.
