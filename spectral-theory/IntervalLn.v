(* ================================================================= *)
(*  IntervalLn.v  --  enclosures of ln, by inverting exp.              *)
(*                                                                    *)
(*    Iln_bisect : Icontains (Iln_bisect ...) (ln (Q2R u))             *)
(*    Ipow_neg34 : Icontains (Ipow_neg34 ...) (Rpower (Q2R u) (-3/4))  *)
(*                                                                    *)
(*  Stage 4a, third and last brick.  The integrand of Re TC needs both *)
(*  ln u (inside the cosine) and u^{-3/4}.                             *)
(*                                                                    *)
(*  NO SERIES FOR ln IS PROVED HERE, and that is the point.  Stdlib    *)
(*  has no ln series at all -- no ps_ln to match Ratan's ps_atan -- so  *)
(*  the ln(1+x) or 2 artanh((u-1)/(u+1)) routes would each require      *)
(*  defining the series, proving convergence, and identifying the      *)
(*  limit with ln.  Instead ln is obtained by INVERTING the exp        *)
(*  enclosure already built: exp is increasing and ln_exp is exact, so  *)
(*                                                                    *)
(*      hi (Iexp a) <= u   ==>   a <= ln u,                            *)
(*      u <= lo (Iexp b)   ==>   ln u <= b,                            *)
(*                                                                    *)
(*  and bisection narrows the bracket.  Each test is a rational        *)
(*  comparison against a computed exp enclosure, so the whole thing is *)
(*  vm_compute-able and its soundness needs only ln monotonicity.      *)
(*                                                                    *)
(*  The bisection NEVER narrows unless justified: when the exp         *)
(*  enclosure at the midpoint is too wide to decide the comparison,    *)
(*  the step returns the current bracket unchanged.  So soundness is   *)
(*  independent of the precision parameters -- they affect only how    *)
(*  tight the answer is, never whether it is correct.                  *)
(*                                                                    *)
(*  COST, recorded for stage 4b: one Iln is fuel x m interval          *)
(*  multiplications (about 900 at fuel = 45, m = 20).  At a few        *)
(*  thousand quadrature nodes this is the dominant cost of the whole   *)
(*  quadrature.  If it proves too slow the remedy is the substitution  *)
(*  u = e^x, which removes ln from the integrand outright: the         *)
(*  integrand becomes Psi(e^x) e^{x/4} cos(t x/2).  Axiom-clean.       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import IntervalArith IntervalArithFun.
Local Open Scope R_scope.

Lemma exp_le_m : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H. destruct (Rle_lt_or_eq_dec a b H) as [Hlt | Heq].
  - left; apply exp_increasing; exact Hlt.
  - right; rewrite Heq; reflexivity.
Qed.

Lemma Q2R_2 : Q2R 2 = 2.
Proof. unfold Q2R; simpl; field. Qed.

Lemma ln_le_mono : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [H | H].
  - left; apply ln_increasing; assumption.
  - subst y; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  one-sided inversion of the exp enclosure                       *)
(* ----------------------------------------------------------------- *)
Lemma exp_hi_le_ln : forall p m (a u : Q),
  -1 <= Q2R a / INR (2 ^ m) -> Q2R a / INR (2 ^ m) < 1 ->
  Q2R (ihi (Iexp_pt p m a)) <= Q2R u ->
  Q2R a <= ln (Q2R u).
Proof.
  intros p m a u Hlo Hhi Hle.
  destruct (Iexp_pt_sound p m a Hlo Hhi) as [_ Hup].
  assert (Hchain : exp (Q2R a) <= Q2R u) by lra.
  assert (Hpos : 0 < exp (Q2R a)) by apply exp_pos.
  pose proof (ln_le_mono _ _ Hpos Hchain) as H.
  rewrite ln_exp in H. exact H.
Qed.

Lemma ln_le_exp_lo : forall p m (b u : Q),
  -1 <= Q2R b / INR (2 ^ m) -> Q2R b / INR (2 ^ m) < 1 ->
  0 < Q2R u -> Q2R u <= Q2R (ilo (Iexp_pt p m b)) ->
  ln (Q2R u) <= Q2R b.
Proof.
  intros p m b u Hlo Hhi Hu Hle.
  destruct (Iexp_pt_sound p m b Hlo Hhi) as [Hdn _].
  assert (Hchain : Q2R u <= exp (Q2R b)) by lra.
  pose proof (ln_le_mono _ _ Hu Hchain) as H.
  rewrite ln_exp in H. exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  bisection                                                      *)
(* ----------------------------------------------------------------- *)
Fixpoint Iln_bisect (p m fuel : nat) (u lo hi : Q) : Itv :=
  match fuel with
  | O => mkI lo hi
  | S f =>
      let mid := ((lo + hi) / 2)%Q in
      if Qle_bool (ihi (Iexp_pt p m mid)) u
      then Iln_bisect p m f u mid hi
      else if Qle_bool u (ilo (Iexp_pt p m mid))
           then Iln_bisect p m f u lo mid
           else mkI lo hi
  end.

Theorem Iln_bisect_sound : forall p m fuel u lo hi,
  (2 <= m)%nat -> 0 < Q2R u ->
  0 <= Q2R lo -> Q2R hi <= 2 -> Q2R lo <= Q2R hi ->
  Q2R lo <= ln (Q2R u) -> ln (Q2R u) <= Q2R hi ->
  Icontains (Iln_bisect p m fuel u lo hi) (ln (Q2R u)).
Proof.
  intros p m fuel. induction fuel as [| f IH]; intros u lo hi Hm Hu Hl0 Hh2 Hlh Hl Hh.
  - simpl. unfold Icontains; simpl. lra.
  - simpl Iln_bisect.
    set (mid := ((lo + hi) / 2)%Q).
    assert (HQ : Q2R mid = (Q2R lo + Q2R hi) / 2).
    { unfold mid. rewrite Q2R_div by (unfold Qeq; simpl; lia).
      rewrite Q2R_plus, Q2R_2. reflexivity. }
    assert (Hm0 : 0 <= Q2R mid) by lra.
    assert (Hm2 : Q2R mid <= 2) by lra.
    (* the reduction hypotheses hold for every midpoint, since 0 <= mid <= 2 *)
    assert (HN : 4 <= INR (2 ^ m)).
    { assert (H2 : (4 <= 2 ^ m)%nat).
      { destruct m as [| [| m']]; [ lia | lia | ].
        simpl. pose proof (pow2_pos m'). lia. }
      replace 4 with (INR 4) at 1 by (simpl; lra).
      apply le_INR; exact H2. }
    assert (Hred1 : -1 <= Q2R mid / INR (2 ^ m))
      by (apply Rle_trans with 0; [ lra | apply Rle_mult_inv_pos; lra ]).
    assert (Hred2 : Q2R mid / INR (2 ^ m) < 1).
    { apply (Rmult_lt_reg_r (INR (2 ^ m))); [ lra | ].
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
      rewrite Rmult_1_r. lra. }
    destruct (Qle_bool (ihi (Iexp_pt p m mid)) u) eqn:E1.
    + apply Qle_bool_iff, Qle_Rle in E1.
      apply IH; try assumption; try lra.
      apply (exp_hi_le_ln p m mid u); assumption.
    + destruct (Qle_bool u (ilo (Iexp_pt p m mid))) eqn:E2.
      * apply Qle_bool_iff, Qle_Rle in E2.
        apply IH; try assumption; try lra.
        apply (ln_le_exp_lo p m mid u); assumption.
      * unfold Icontains; simpl. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  exp on an INTERVAL, by monotonicity                            *)
(* ----------------------------------------------------------------- *)
Definition Iexp_itv (p m : nat) (i : Itv) : Itv :=
  mkI (ilo (Iexp_pt p m (ilo i))) (ihi (Iexp_pt p m (ihi i))).

Lemma Iexp_itv_sound : forall p m i x,
  -1 <= Q2R (ilo i) / INR (2 ^ m) -> Q2R (ilo i) / INR (2 ^ m) < 1 ->
  -1 <= Q2R (ihi i) / INR (2 ^ m) -> Q2R (ihi i) / INR (2 ^ m) < 1 ->
  Icontains i x -> Icontains (Iexp_itv p m i) (exp x).
Proof.
  intros p m i x Ha1 Ha2 Hb1 Hb2 [Hx1 Hx2].
  destruct (Iexp_pt_sound p m (ilo i) Ha1 Ha2) as [Hl _].
  destruct (Iexp_pt_sound p m (ihi i) Hb1 Hb2) as [_ Hh].
  unfold Icontains, Iexp_itv; simpl. split.
  - eapply Rle_trans; [ exact Hl | ]. apply exp_le_m; exact Hx1.
  - eapply Rle_trans; [ | exact Hh ]. apply exp_le_m; exact Hx2.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  u^{-3/4} = exp (-(3/4) ln u)                                   *)
(* ----------------------------------------------------------------- *)
(*  The ln enclosure is taken as an ARGUMENT rather than computed here, *)
(*  so the two bricks compose without this file having to re-establish  *)
(*  that Iln_bisect stays inside its initial bracket.  The caller       *)
(*  passes L := Iln_bisect p m fuel u 0 2 and discharges the reduction  *)
(*  side conditions by computation.                                    *)
Lemma Q2R_m34 : Q2R (-3 # 4) = -(3/4).
Proof. unfold Q2R; simpl; field. Qed.

Definition Ipow_neg34 (p m : nat) (L : Itv) : Itv :=
  Iexp_itv p m (Imul (Iconst (-3 # 4)) L).

Theorem Ipow_neg34_sound : forall p m L u,
  0 < u -> Icontains L (ln u) ->
  (let S := Imul (Iconst (-3 # 4)) L in
   -1 <= Q2R (ilo S) / INR (2 ^ m) /\ Q2R (ilo S) / INR (2 ^ m) < 1 /\
   -1 <= Q2R (ihi S) / INR (2 ^ m) /\ Q2R (ihi S) / INR (2 ^ m) < 1) ->
  Icontains (Ipow_neg34 p m L) (Rpower u (-(3/4))).
Proof.
  intros p m L u Hu HL Hred. simpl in Hred.
  destruct Hred as [Ha1 [Ha2 [Hb1 Hb2]]].
  assert (HS : Icontains (Imul (Iconst (-3 # 4)) L) (-(3/4) * ln u)).
  { rewrite <- Q2R_m34. apply Imul_sound; [ apply Iconst_sound | exact HL ]. }
  unfold Ipow_neg34, Rpower.
  apply Iexp_itv_sound; assumption.
Qed.

Print Assumptions Iln_bisect_sound.
Print Assumptions Iexp_itv_sound.
Print Assumptions Ipow_neg34_sound.
