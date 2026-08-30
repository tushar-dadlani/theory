(* ================================================================= *)
(*  XirSignChange.v  --  the accumulated midpoint sum, and the sign.   *)
(*                                                                    *)
(*    Imsum ... n = Some i  ->  Icontains i (msum (gint t) 0 h n)      *)
(*    xir_pos_of / xir_neg_of : an enclosure of msum, plus numeric     *)
(*      bounds on the two error terms, decides the sign of xir t.      *)
(*                                                                    *)
(*  Stage 4c, the last structural brick.  ReTCQuad.ReTC_quadrature     *)
(*  reduced Re TC to msum plus a proved error; IntervalGint evaluates  *)
(*  the integrand at one rational node; this accumulates the sum in    *)
(*  interval arithmetic and converts the result into a sign for xir    *)
(*  through XirIntegralReduction.xir_reduction'.                       *)
(*                                                                    *)
(*  Iround after EVERY accumulation is not an optimisation, it is      *)
(*  what makes the computation finish: Qplus on Q is                   *)
(*  cross-multiplication and never reduces, so an unrounded sum of n   *)
(*  terms carries the PRODUCT of all n denominators.                   *)
(*                                                                    *)
(*  The sign lemmas are stated against ABSTRACT bounds EM (on Mfin)    *)
(*  and ET (on the truncation) rather than numerals, so the structure  *)
(*  is independent of how sharply those two transcendental constants   *)
(*  are pinned down.  Axiom-clean.                                     *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import ComplexField IntervalArith IntervalArithFun IntervalCos IntervalLn
        CoherenceSingularity ThetaTailEntire XirIntegralReduction
        RiemannPsi PsiXSpace PsiXDeriv IntegrandLip CompositeQuad
        ReTCTailBound ReTCQuad IntervalGint SimpsonQuad.
Local Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the midpoint nodes, as rationals                              *)
(* ----------------------------------------------------------------- *)
Definition Inode (hq : Q) (k : nat) : Q :=
  (2 * inject_Z (Z.of_nat k) + 1) / 2 * hq.

Lemma Q2R_Inode : forall hq k, Q2R (Inode hq k) = (INR k + / 2) * Q2R hq.
Proof.
  intros hq k. unfold Inode.
  rewrite Q2R_mult, Q2R_div by (apply inject_Z_neq0; lia).
  rewrite Q2R_plus, Q2R_mult, Q2R_inject, (Q2R_lit 2), (Q2R_lit 1).
  rewrite INR_IZR_INZ. field.
Qed.

Lemma Inode_nonneg : forall hq k, 0 <= Q2R hq -> 0 <= Q2R (Inode hq k).
Proof.
  intros hq k Hh. rewrite Q2R_Inode.
  apply Rmult_le_pos; [ | exact Hh ].
  pose proof (pos_INR k). lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the accumulated sum                                           *)
(* ----------------------------------------------------------------- *)
Fixpoint Imsum (p m p2 m2 p3 m3 pc mc nc pr : nat) (tq hq : Q) (n : nat)
  : option Itv :=
  match n with
  | O => Some (Iconst 0)
  | S k =>
      match Imsum p m p2 m2 p3 m3 pc mc nc pr tq hq k,
            Igint p m p2 m2 p3 m3 pc mc nc tq (Inode hq k) with
      | Some acc, Some v => Some (Iround pr (Iadd acc (Imul (Iconst hq) v)))
      | _, _ => None
      end
  end.

Theorem Imsum_sound : forall p m p2 m2 p3 m3 pc mc nc pr tq hq n i,
  0 <= Q2R hq ->
  Imsum p m p2 m2 p3 m3 pc mc nc pr tq hq n = Some i ->
  Icontains i (msum (gint (Q2R tq)) 0 (Q2R hq) n).
Proof.
  intros p m p2 m2 p3 m3 pc mc nc pr tq hq n.
  induction n as [| k IH]; intros i Hh H.
  - cbn [Imsum msum] in *. injection H as <-.
    replace 0 with (Q2R 0) by (unfold Q2R; simpl; lra).
    apply Iconst_sound.
  - cbn [Imsum] in H.
    destruct (Imsum p m p2 m2 p3 m3 pc mc nc pr tq hq k) as [acc |] eqn:Ha;
      [ | discriminate ].
    destruct (Igint p m p2 m2 p3 m3 pc mc nc tq (Inode hq k)) as [v |] eqn:Hv;
      [ | discriminate ].
    injection H as <-.
    pose proof (IH acc Hh eq_refl) as Hacc.
    pose proof (Igint_sound p m p2 m2 p3 m3 pc mc nc tq (Inode hq k) v
                  (Inode_nonneg hq k Hh) Hv) as Hgv.
    rewrite Q2R_Inode in Hgv.
    cbn [msum].
    replace (0 + (INR k + / 2) * Q2R hq) with ((INR k + / 2) * Q2R hq) by ring.
    apply Iround_sound, Iadd_sound; [ exact Hacc | ].
    apply Imul_sound; [ apply Iconst_sound | exact Hgv ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  from an enclosure of msum to the sign of xir                  *)
(* ----------------------------------------------------------------- *)
Section Sign.

Variable t L : R.
Variable n : nat.
Variable EM ET : R.

Hypothesis Hn : (0 < n)%nat.
Hypothesis HL : 0 <= L.
Hypothesis HEM : Mfin t L <= EM.
Hypothesis HET : Cc * exp (- (PI * exp L)) / PI <= ET.

Let err : R := EM * L ^ 3 / (24 * INR n ^ 2) + ET.

Lemma ReTC_enclosed :
  Rabs (Re (TC (crit t)) - msum (gint t) 0 (L / INR n) n) <= err.
Proof.
  pose proof (ReTC_quadrature t L n Hn HL) as H.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hpos : 0 < 24 * INR n ^ 2) by nra.
  assert (HQ : Mfin t L * L ^ 3 / (24 * INR n ^ 2)
               <= EM * L ^ 3 / (24 * INR n ^ 2)).
  { unfold Rdiv. apply Rmult_le_compat_r.
    - left; apply Rinv_0_lt_compat; exact Hpos.
    - apply Rmult_le_compat_r; [ apply pow_le; exact HL | exact HEM ]. }
  unfold err. lra.
Qed.

Theorem xir_pos_of : forall S,
  msum (gint t) 0 (L / INR n) n <= S ->
  S + err < / (2 * (/ 4 + t ^ 2)) ->
  0 < / 4 + t ^ 2 ->
  0 < xir t.
Proof.
  intros S HS Hlt Hq. rewrite xir_reduction'.
  pose proof ReTC_enclosed as HE.
  assert (Hup : Re (TC (crit t)) <= S + err).
  { pose proof (Rle_abs (Re (TC (crit t))
                         - msum (gint t) 0 (L / INR n) n)) as H1. lra. }
  assert (Hkey : Re (TC (crit t)) < / (2 * (/ 4 + t ^ 2))) by lra.
  assert (Hprod : (/ 4 + t ^ 2) * Re (TC (crit t)) < / 2).
  { apply (Rmult_lt_reg_l (/ (/ 4 + t ^ 2))).
    - apply Rinv_0_lt_compat; exact Hq.
    - assert (E1 : / (/ 4 + t ^ 2) * ((/ 4 + t ^ 2) * Re (TC (crit t)))
                 = Re (TC (crit t))) by (field; lra).
      assert (E2 : / (/ 4 + t ^ 2) * / 2 = / (2 * (/ 4 + t ^ 2)))
        by (field; lra).
      rewrite E1, E2. exact Hkey. }
  lra.
Qed.

Theorem xir_neg_of : forall S,
  S <= msum (gint t) 0 (L / INR n) n ->
  / (2 * (/ 4 + t ^ 2)) < S - err ->
  0 < / 4 + t ^ 2 ->
  xir t < 0.
Proof.
  intros S HS Hlt Hq. rewrite xir_reduction'.
  pose proof ReTC_enclosed as HE.
  assert (Hlo : S - err <= Re (TC (crit t))).
  { pose proof (Rle_abs (- (Re (TC (crit t))
                            - msum (gint t) 0 (L / INR n) n))) as H1.
    rewrite Rabs_Ropp in H1. lra. }
  assert (Hkey : / (2 * (/ 4 + t ^ 2)) < Re (TC (crit t))) by lra.
  assert (Hprod : / 2 < (/ 4 + t ^ 2) * Re (TC (crit t))).
  { apply (Rmult_lt_reg_l (/ (/ 4 + t ^ 2))).
    - apply Rinv_0_lt_compat; exact Hq.
    - assert (E1 : / (/ 4 + t ^ 2) * ((/ 4 + t ^ 2) * Re (TC (crit t)))
                 = Re (TC (crit t))) by (field; lra).
      assert (E2 : / (/ 4 + t ^ 2) * / 2 = / (2 * (/ 4 + t ^ 2)))
        by (field; lra).
      rewrite E1, E2. exact Hkey. }
  lra.
Qed.

End Sign.

(* ----------------------------------------------------------------- *)
(*  D.  the sign rule with the error ABSTRACT                          *)
(*                                                                    *)
(*  The two lemmas above tie the error to the midpoint rule's shape.   *)
(*  These take it as a parameter, so the Simpson route feeds the same  *)
(*  algebra without duplicating it.  The section versions are the      *)
(*  special case S = msum, err = EM L^3/(24 n^2) + ET.                 *)
(* ----------------------------------------------------------------- *)
Theorem xir_pos_of_gen : forall t S err,
  Rabs (Re (TC (crit t)) - S) <= err ->
  S + err < / (2 * (/ 4 + t ^ 2)) ->
  0 < / 4 + t ^ 2 ->
  0 < xir t.
Proof.
  intros t S err HE Hlt Hq. rewrite xir_reduction'.
  assert (Hup : Re (TC (crit t)) <= S + err).
  { pose proof (Rle_abs (Re (TC (crit t)) - S)) as H1. lra. }
  assert (Hkey : Re (TC (crit t)) < / (2 * (/ 4 + t ^ 2))) by lra.
  assert (Hprod : (/ 4 + t ^ 2) * Re (TC (crit t)) < / 2).
  { apply (Rmult_lt_reg_l (/ (/ 4 + t ^ 2))).
    - apply Rinv_0_lt_compat; exact Hq.
    - assert (E1 : / (/ 4 + t ^ 2) * ((/ 4 + t ^ 2) * Re (TC (crit t)))
                 = Re (TC (crit t))) by (field; lra).
      assert (E2 : / (/ 4 + t ^ 2) * / 2 = / (2 * (/ 4 + t ^ 2)))
        by (field; lra).
      rewrite E1, E2. exact Hkey. }
  lra.
Qed.

Theorem xir_neg_of_gen : forall t S err,
  Rabs (Re (TC (crit t)) - S) <= err ->
  / (2 * (/ 4 + t ^ 2)) < S - err ->
  0 < / 4 + t ^ 2 ->
  xir t < 0.
Proof.
  intros t S err HE Hlt Hq. rewrite xir_reduction'.
  assert (Hlo : S - err <= Re (TC (crit t))).
  { pose proof (Rle_abs (- (Re (TC (crit t)) - S))) as H1.
    rewrite Rabs_Ropp in H1. lra. }
  assert (Hkey : / (2 * (/ 4 + t ^ 2)) < Re (TC (crit t))) by lra.
  assert (Hprod : / 2 < (/ 4 + t ^ 2) * Re (TC (crit t))).
  { apply (Rmult_lt_reg_l (/ (/ 4 + t ^ 2))).
    - apply Rinv_0_lt_compat; exact Hq.
    - assert (E1 : / (/ 4 + t ^ 2) * ((/ 4 + t ^ 2) * Re (TC (crit t)))
                 = Re (TC (crit t))) by (field; lra).
      assert (E2 : / (/ 4 + t ^ 2) * / 2 = / (2 * (/ 4 + t ^ 2)))
        by (field; lra).
      rewrite E1, E2. exact Hkey. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the interval SIMPSON sum                                       *)
(*                                                                    *)
(*  Panels are self-contained (SimpsonQuad.ssum), so each contributes  *)
(*  three Igint evaluations combined as (h/6)(f_l + 4 f_m + f_r).      *)
(*  Shared nodes are evaluated twice -- 3n calls instead of 2n+1 --    *)
(*  which at n = 512 is 1536 against 1025, and buys a Fixpoint whose   *)
(*  induction matches ssum's exactly.                                  *)
(*                                                                    *)
(*  As with Imsum, Iround after EVERY accumulation is what makes this  *)
(*  terminate: Qplus never reduces, so an unrounded sum of n terms     *)
(*  carries the product of all n denominators.                        *)
(* ----------------------------------------------------------------- *)
Definition Inodek (hq : Q) (k : nat) : Q := inject_Z (Z.of_nat k) * hq.
Definition Inodem (hq : Q) (k : nat) : Q :=
  (2 * inject_Z (Z.of_nat k) + 1) / 2 * hq.

Lemma Q2R_Inodek : forall hq k, Q2R (Inodek hq k) = INR k * Q2R hq.
Proof.
  intros hq k. unfold Inodek.
  rewrite Q2R_mult, Q2R_inject, INR_IZR_INZ. reflexivity.
Qed.

Lemma Q2R_Inodem : forall hq k, Q2R (Inodem hq k) = (INR k + / 2) * Q2R hq.
Proof.
  intros hq k. unfold Inodem.
  rewrite Q2R_mult, Q2R_div by (apply inject_Z_neq0; lia).
  rewrite Q2R_plus, Q2R_mult, Q2R_inject, (Q2R_lit 2), (Q2R_lit 1).
  rewrite INR_IZR_INZ. field.
Qed.

Lemma Inodek_nonneg : forall hq k, 0 <= Q2R hq -> 0 <= Q2R (Inodek hq k).
Proof.
  intros hq k Hh. rewrite Q2R_Inodek.
  apply Rmult_le_pos; [ apply pos_INR | exact Hh ].
Qed.

Lemma Inodem_nonneg : forall hq k, 0 <= Q2R hq -> 0 <= Q2R (Inodem hq k).
Proof.
  intros hq k Hh. rewrite Q2R_Inodem.
  apply Rmult_le_pos; [ pose proof (pos_INR k); lra | exact Hh ].
Qed.

Fixpoint Issum (p m p2 m2 p3 m3 pc mc nc pr : nat) (tq hq : Q) (n : nat)
  : option Itv :=
  match n with
  | O => Some (Iconst 0)
  | S k =>
      match Issum p m p2 m2 p3 m3 pc mc nc pr tq hq k,
            Igint p m p2 m2 p3 m3 pc mc nc tq (Inodek hq k),
            Igint p m p2 m2 p3 m3 pc mc nc tq (Inodem hq k),
            Igint p m p2 m2 p3 m3 pc mc nc tq (Inodek hq (S k)) with
      | Some acc, Some vl, Some vm, Some vr =>
          Some (Iround pr
                  (Iadd acc
                     (Imul (Iconst (hq / 6))
                        (Iadd (Iadd vl (Imul (Iconst 4) vm)) vr))))
      | _, _, _, _ => None
      end
  end.

Theorem Issum_sound : forall p m p2 m2 p3 m3 pc mc nc pr tq hq n i,
  0 <= Q2R hq ->
  Issum p m p2 m2 p3 m3 pc mc nc pr tq hq n = Some i ->
  Icontains i (ssum (gint (Q2R tq)) 0 (Q2R hq) n).
Proof.
  intros p m p2 m2 p3 m3 pc mc nc pr tq hq n.
  induction n as [| k IH]; intros i Hh H.
  - cbn [Issum ssum] in *. injection H as <-.
    replace 0 with (Q2R 0) by (unfold Q2R; simpl; lra).
    apply Iconst_sound.
  - cbn [Issum] in H.
    destruct (Issum p m p2 m2 p3 m3 pc mc nc pr tq hq k) as [acc |] eqn:Ha;
      [ | discriminate ].
    destruct (Igint p m p2 m2 p3 m3 pc mc nc tq (Inodek hq k)) as [vl |] eqn:Hl;
      [ | discriminate ].
    destruct (Igint p m p2 m2 p3 m3 pc mc nc tq (Inodem hq k)) as [vm |] eqn:Hm;
      [ | discriminate ].
    destruct (Igint p m p2 m2 p3 m3 pc mc nc tq (Inodek hq (S k)))
      as [vr |] eqn:Hr; [ | discriminate ].
    injection H as <-.
    pose proof (IH acc Hh eq_refl) as Hacc.
    pose proof (Igint_sound p m p2 m2 p3 m3 pc mc nc tq (Inodek hq k) vl
                  (Inodek_nonneg hq k Hh) Hl) as Gl.
    pose proof (Igint_sound p m p2 m2 p3 m3 pc mc nc tq (Inodem hq k) vm
                  (Inodem_nonneg hq k Hh) Hm) as Gm.
    pose proof (Igint_sound p m p2 m2 p3 m3 pc mc nc tq (Inodek hq (S k)) vr
                  (Inodek_nonneg hq (S k) Hh) Hr) as Gr.
    rewrite Q2R_Inodek in Gl, Gr. rewrite Q2R_Inodem in Gm.
    cbn [ssum].
    replace (0 + INR k * Q2R hq) with (INR k * Q2R hq) by ring.
    replace (0 + (INR k + / 2) * Q2R hq) with ((INR k + / 2) * Q2R hq) by ring.
    replace (0 + INR (S k) * Q2R hq) with (INR (S k) * Q2R hq) by ring.
    apply Iround_sound, Iadd_sound; [ exact Hacc | ].
    assert (Eh : Q2R hq / 6 = Q2R (hq / 6)).
    { rewrite Q2R_div by (apply inject_Z_neq0; lia).
      rewrite (Q2R_lit 6). reflexivity. }
    rewrite Eh.
    apply Imul_sound; [ apply Iconst_sound | ].
    apply Iadd_sound; [ apply Iadd_sound | exact Gr ].
    + exact Gl.
    + apply Imul_sound; [ | exact Gm ].
      replace 4 with (Q2R (4 # 1)) by (rewrite Q2R_lit; simpl; lra).
      apply Iconst_sound.
Qed.

Print Assumptions Issum_sound.
Print Assumptions xir_pos_of_gen.
Print Assumptions xir_neg_of_gen.
Print Assumptions Imsum_sound.
Print Assumptions xir_pos_of.
Print Assumptions xir_neg_of.
