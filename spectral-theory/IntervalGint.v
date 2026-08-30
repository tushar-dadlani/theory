(* ================================================================= *)
(*  IntervalGint.v  --  interval evaluation of gint t at a rational.   *)
(*                                                                    *)
(*    Igint p m mc nc t x = Some i  ->  Icontains i (gint t (Q2R x))   *)
(*                                                                    *)
(*  Stage 4c, the computational brick.  gint t x = Psi(e^x) e^{x/4}    *)
(*  cos(tx/2) is assembled from Iexp_pt (the e^{x/4} factor and the    *)
(*  inner e^x), Iexp_itv (Psi's three exponentials, whose ARGUMENTS    *)
(*  are themselves intervals because pi is), and Icos_pt.  Psi itself  *)
(*  enters through PsiXSpace.Psi_simple, whose upper bound was built   *)
(*  with a rational tail constant precisely so that no reciprocal is   *)
(*  needed -- IntervalArith has no Iinv.                               *)
(*                                                                    *)
(*  The design point is the GUARDS.  Iexp_pt is sound only when its    *)
(*  argument, after m halvings, lands in [-1,1); Icos_pt only when its *)
(*  argument lands in [-pi/2, pi/2].  Those are conditions on          *)
(*  intermediate intervals which no caller can predict, because        *)
(*  Icontains bounds nothing about an interval's WIDTH -- soundness    *)
(*  alone does not say Iexp_pt returns something narrow.  So the       *)
(*  guards are folded into the computation and the result is an        *)
(*  option: the checks are decided by vm_compute along with everything *)
(*  else, and the soundness lemma is then UNCONDITIONAL on the         *)
(*  intervals (it still needs 0 <= x, which is about the node, not     *)
(*  about any computed enclosure).                                     *)
(*                                                                    *)
(*  pi is bracketed by CertifiedPi.PI_enclosure, [3.14159, 3.1416].    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia Bool.
Require Import IntervalArith IntervalArithFun IntervalCos IntervalLn
        CertifiedPi RiemannPsi PsiXSpace PsiXDeriv IntegrandLip.
Local Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  small Q2R facts                                               *)
(* ----------------------------------------------------------------- *)
Lemma Q2R_lit : forall z : Z, Q2R (z # 1) = IZR z.
Proof. intro z. unfold Q2R; simpl. field. Qed.

Lemma Qle_R : forall a b : Q, Qle_bool a b = true -> Q2R a <= Q2R b.
Proof. intros a b H. apply Qle_Rle. apply Qle_bool_iff. exact H. Qed.

Lemma Q2R_half_scale : forall m q, Q2R (q / Qp2 m) = Q2R q / INR (2 ^ m).
Proof.
  intros m q. rewrite Q2R_div by apply Qp2_neq0. rewrite Q2R_Qp2. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  pi, as an interval                                            *)
(* ----------------------------------------------------------------- *)
(* PI to 1.3e-9.  This width is inherited MULTIPLICATIVELY by every    *)
(* e^{-pi u} below -- the enclosure of that acquires a relative width   *)
(* of about (width of Ipi) x u -- so at the previous 1e-5 it was ALONE  *)
(* the entire 1.25e-7 width of the accumulated midpoint sum.           *)
Definition Ipi : Itv := mkI (31415926533 # 10000000000)
                            (31415926546 # 10000000000).

Lemma Ipi_sound : Icontains Ipi PI.
Proof.
  unfold Icontains, Ipi; simpl. split.
  - eapply Rle_trans; [ | apply PI_lower ]. unfold Q2R; simpl; lra.
  - eapply Rle_trans; [ apply PI_upper | ]. unfold Q2R; simpl; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  guarded transcendentals                                       *)
(* ----------------------------------------------------------------- *)
Definition inrange (m : nat) (q : Q) : bool :=
  Qle_bool (- (1)) (q / Qp2 m) && Qle_bool (q / Qp2 m) (1 # 2).

Lemma inrange_ok : forall m q, inrange m q = true ->
  -1 <= Q2R q / INR (2 ^ m) /\ Q2R q / INR (2 ^ m) < 1.
Proof.
  intros m q H. unfold inrange in H.
  apply andb_true_iff in H as [H1 H2].
  apply Qle_R in H1. apply Qle_R in H2.
  rewrite Q2R_half_scale in H1, H2.
  assert (E1 : Q2R (- (1)) = -1) by (unfold Q2R; simpl; lra).
  assert (E2 : Q2R (1 # 2) = / 2) by (unfold Q2R; simpl; lra).
  rewrite E1 in H1. rewrite E2 in H2. lra.
Qed.

Definition Iexp_ptc (p m : nat) (q : Q) : option Itv :=
  if inrange m q then Some (Iexp_pt p m q) else None.

Lemma Iexp_ptc_sound : forall p m q i,
  Iexp_ptc p m q = Some i -> Icontains i (exp (Q2R q)).
Proof.
  intros p m q i H. unfold Iexp_ptc in H.
  destruct (inrange m q) eqn:Hg; [ | discriminate ].
  injection H as <-. destruct (inrange_ok m q Hg) as [H1 H2].
  apply Iexp_pt_sound; assumption.
Qed.

Definition Iexp_itvc (p m : nat) (j : Itv) : option Itv :=
  if inrange m (ilo j) && inrange m (ihi j)
  then Some (Iexp_itv p m j) else None.

Lemma Iexp_itvc_sound : forall p m j i x,
  Iexp_itvc p m j = Some i -> Icontains j x -> Icontains i (exp x).
Proof.
  intros p m j i x H Hx. unfold Iexp_itvc in H.
  destruct (inrange m (ilo j) && inrange m (ihi j)) eqn:Hg; [ | discriminate ].
  injection H as <-. apply andb_true_iff in Hg as [Ha Hb].
  destruct (inrange_ok m (ilo j) Ha) as [A1 A2].
  destruct (inrange_ok m (ihi j) Hb) as [B1 B2].
  apply Iexp_itv_sound; assumption.
Qed.

Definition inrangec (m : nat) (q : Q) : bool :=
  Qle_bool (- (157 # 100)) (q / Qp2 m) && Qle_bool (q / Qp2 m) (157 # 100).

Definition Icos_ptc (p m n : nat) (q : Q) : option Itv :=
  if inrangec m q then Some (Icos_pt p m n q) else None.

Lemma Icos_ptc_sound : forall p m n q i,
  Icos_ptc p m n q = Some i -> Icontains i (cos (Q2R q)).
Proof.
  intros p m n q i H. unfold Icos_ptc in H.
  destruct (inrangec m q) eqn:Hg; [ | discriminate ].
  injection H as <-. unfold inrangec in Hg.
  apply andb_true_iff in Hg as [H1 H2].
  apply Qle_R in H1. apply Qle_R in H2.
  rewrite Q2R_half_scale in H1, H2.
  assert (E1 : Q2R (- (157 # 100)) = - (157 / 100)) by (unfold Q2R; simpl; lra).
  assert (E2 : Q2R (157 # 100) = 157 / 100) by (unfold Q2R; simpl; lra).
  rewrite E1 in H1. rewrite E2 in H2.
  pose proof PI_lower as HP.
  apply Icos_pt_sound; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  Psi(e^x)                                                      *)
(* ----------------------------------------------------------------- *)
(* keep Iadd/Imul FOLDED: cbn on the projections would unfold them in the
   goal but not in the hypotheses, and the atoms would stop matching *)
Lemma Icontains_mk : forall (i j : Itv) x,
  Q2R (ilo i) <= x -> x <= Q2R (ihi j) -> Icontains (mkI (ilo i) (ihi j)) x.
Proof. intros i j x H1 H2. unfold Icontains; simpl. split; assumption. Qed.

(* three separate precisions: e^{-pi u} carries the whole value (~4e-2)
   and needs ~1e-7 absolute; e^{-4 pi u} is ~3e-6 and e^{-9 pi u} ~6e-13,
   so computing them at the same cost is pure waste.  Measured: ~40% of
   the per-node time. *)
Definition IPsi_x (p m p2 m2 p3 m3 : nat) (xq : Q) : option Itv :=
  match Iexp_ptc p m xq with
  | None => None
  | Some Ex =>
      let A1 := Imul (Ineg Ipi) Ex in
      match Iexp_itvc p m A1,
            Iexp_itvc p2 m2 (Imul (Iconst 4) A1),
            Iexp_itvc p3 m3 (Imul (Iconst 9) A1) with
      | Some E1, Some E2, Some E3 =>
          Some (mkI (ilo (Iadd E1 E2))
                    (ihi (Iadd (Iadd E1 E2) (Imul (Iconst 2) E3))))
      | _, _, _ => None
      end
  end.

Lemma IPsi_x_sound : forall p m p2 m2 p3 m3 xq i, 0 <= Q2R xq ->
  IPsi_x p m p2 m2 p3 m3 xq = Some i -> Icontains i (Psi (exp (Q2R xq))).
Proof.
  intros p m p2 m2 p3 m3 xq i Hx H. unfold IPsi_x in H.
  destruct (Iexp_ptc p m xq) as [Ex |] eqn:HE; [ | discriminate ].
  pose proof (Iexp_ptc_sound p m xq Ex HE) as HEx.
  set (u := exp (Q2R xq)) in *.
  assert (Hu : 1 <= u) by (unfold u; apply exp_ge_1; exact Hx).
  set (A1 := Imul (Ineg Ipi) Ex) in *.
  assert (HA1 : Icontains A1 (- PI * u))
    by (apply Imul_sound; [ apply Ineg_sound; apply Ipi_sound | exact HEx ]).
  assert (H4 : Icontains (Imul (Iconst 4) A1) (4 * (- PI * u))).
  { apply Imul_sound; [ | exact HA1 ].
    replace 4 with (Q2R (4 # 1)) by (rewrite Q2R_lit; simpl; lra).
    apply Iconst_sound. }
  assert (H9 : Icontains (Imul (Iconst 9) A1) (9 * (- PI * u))).
  { apply Imul_sound; [ | exact HA1 ].
    replace 9 with (Q2R (9 # 1)) by (rewrite Q2R_lit; simpl; lra).
    apply Iconst_sound. }
  destruct (Iexp_itvc p m A1) as [E1 |] eqn:HE1; [ | discriminate ].
  destruct (Iexp_itvc p2 m2 (Imul (Iconst 4) A1)) as [E2 |] eqn:HE2; [ | discriminate ].
  destruct (Iexp_itvc p3 m3 (Imul (Iconst 9) A1)) as [E3 |] eqn:HE3; [ | discriminate ].
  injection H as <-.
  pose proof (Iexp_itvc_sound p m A1 E1 _ HE1 HA1) as G1.
  pose proof (Iexp_itvc_sound p2 m2 _ E2 _ HE2 H4) as G2.
  pose proof (Iexp_itvc_sound p3 m3 _ E3 _ HE3 H9) as G3.
  (* line the exponents up with Psi_simple's *)
  replace (- PI * u) with (- (PI * u)) in G1 by ring.
  replace (4 * (- PI * u)) with (- (PI * 4 * u)) in G2 by ring.
  replace (9 * (- PI * u)) with (- (9 * (PI * u))) in G3 by ring.
  assert (H2E3 : Icontains (Imul (Iconst 2) E3) (2 * exp (- (9 * (PI * u))))).
  { apply Imul_sound; [ | exact G3 ].
    replace 2 with (Q2R (2 # 1)) by (rewrite Q2R_lit; simpl; lra).
    apply Iconst_sound. }
  pose proof (Iadd_sound E1 E2 _ _ G1 G2) as Hsum.
  pose proof (Iadd_sound _ _ _ _ Hsum H2E3) as Hsum3.
  destruct (Psi_simple u Hu) as [Plo Phi].
  destruct Hsum as [Hs1 _]. destruct Hsum3 as [_ Hs2].
  cbn [ilo ihi Iadd Imul Iconst Ineg] in Hs1, Hs2 |- *.
  unfold Icontains; cbn [ilo ihi]. split; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the whole integrand                                           *)
(* ----------------------------------------------------------------- *)
Definition Igint (p m p2 m2 p3 m3 pc mc nc : nat) (tq xq : Q) : option Itv :=
  match IPsi_x p m p2 m2 p3 m3 xq, Iexp_ptc p m (xq / 4),
        Icos_ptc pc mc nc (tq / 2 * xq) with
  | Some P, Some E, Some C => Some (Imul (Imul P E) C)
  | _, _, _ => None
  end.

Theorem Igint_sound : forall p m p2 m2 p3 m3 pc mc nc tq xq i, 0 <= Q2R xq ->
  Igint p m p2 m2 p3 m3 pc mc nc tq xq = Some i ->
  Icontains i (gint (Q2R tq) (Q2R xq)).
Proof.
  intros p m p2 m2 p3 m3 pc mc nc tq xq i Hx H. unfold Igint in H.
  destruct (IPsi_x p m p2 m2 p3 m3 xq) as [P |] eqn:HP; [ | discriminate ].
  destruct (Iexp_ptc p m (xq / 4)) as [E |] eqn:HE; [ | discriminate ].
  destruct (Icos_ptc pc mc nc (tq / 2 * xq)) as [C |] eqn:HC; [ | discriminate ].
  injection H as <-.
  pose proof (IPsi_x_sound p m p2 m2 p3 m3 xq P Hx HP) as GP.
  pose proof (Iexp_ptc_sound p m (xq / 4) E HE) as GE.
  pose proof (Icos_ptc_sound pc mc nc (tq / 2 * xq) C HC) as GC.
  assert (E4 : Q2R (xq / 4) = / 4 * Q2R xq).
  { rewrite Q2R_div by (apply inject_Z_neq0; lia).
    rewrite (Q2R_lit 4). field. }
  assert (Ec : Q2R (tq / 2 * xq) = Q2R tq / 2 * Q2R xq).
  { rewrite Q2R_mult, Q2R_div by (apply inject_Z_neq0; lia).
    rewrite (Q2R_lit 2). reflexivity. }
  rewrite E4 in GE. rewrite Ec in GC.
  unfold gint, GPsi, Qe, Ct.
  apply Imul_sound; [ apply Imul_sound | ]; assumption.
Qed.

Print Assumptions Ipi_sound.
Print Assumptions IPsi_x_sound.
Print Assumptions Igint_sound.
