(* ================================================================= *)
(*  CompositeQuad.v  --  the COMPOSITE midpoint rule.                  *)
(*                                                                    *)
(*    msum f a h n  =  sum_{k<n} h . f(a + (k + 1/2) h)                *)
(*                                                                    *)
(*    composite_midpoint :                                            *)
(*      |int_a^{a+n h} f - msum f a h n|  <=  n . M h^3 / 24           *)
(*                                                                    *)
(*  Stage 4b, closing brick.  MidpointQuad.midpoint_single bounds ONE  *)
(*  panel; the quadrature needs the whole interval, so the panels must *)
(*  be glued.  The glue is RiemannInt_P26 (additivity) plus the        *)
(*  triangle inequality, by induction on n.                            *)
(*                                                                    *)
(*  The one real friction is dependent typing: Riemann_integrable f a  *)
(*  b mentions b in its TYPE, and the induction naturally produces     *)
(*  endpoints written two different ways -- a + INR (S n) * h from the *)
(*  statement, c + h/2 from midpoint_single's panel-centred form.      *)
(*  These are equal as reals but not definitionally, so RI_endpoint    *)
(*  transports along the equality (RiemannInt_P5 after subst).  The    *)
(*  integrability proofs themselves are never threaded through the     *)
(*  induction: they are regenerated at each endpoint from continuity,  *)
(*  which is free because differentiability is already assumed.        *)
(*                                                                    *)
(*  Rate: with h = (b-a)/n the bound reads M (b-a)^3 / (24 n^2) -- the  *)
(*  classical composite-midpoint constant exactly, now that            *)
(*  MidpointQuad proves the sharp Taylor remainder M2 (x-c)^2/2.       *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import MidpointQuad.
Open Scope R_scope.

Fixpoint msum (f : R -> R) (a h : R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => msum f a h k + h * f (a + (INR k + / 2) * h)
  end.

(* transport an integral along an equality of endpoints *)
Lemma RI_endpoint : forall f a b b'
  (pr : Riemann_integrable f a b) (pr' : Riemann_integrable f a b'),
  b = b' -> RiemannInt pr = RiemannInt pr'.
Proof. intros f a b b' pr pr' E. subst b'. apply RiemannInt_P5. Qed.

Lemma cont_of_deriv : forall (f f' : R -> R) A B,
  (forall y, A <= y <= B -> derivable_pt_lim f y (f' y)) ->
  forall y, A <= y <= B -> continuity_pt f y.
Proof.
  intros f f' A B Hd y Hy. apply derivable_continuous_pt.
  exists (f' y). apply Hd; exact Hy.
Qed.

Theorem composite_midpoint : forall (f f' : R -> R) (a h M : R) (n : nat)
  (pr : Riemann_integrable f a (a + INR n * h)),
  0 <= h -> 0 <= M ->
  (forall y, a <= y <= a + INR n * h -> derivable_pt_lim f y (f' y)) ->
  (forall y z, a <= y <= a + INR n * h -> a <= z <= a + INR n * h ->
     Rabs (f' y - f' z) <= M * Rabs (y - z)) ->
  Rabs (RiemannInt pr - msum f a h n) <= INR n * (M * h ^ 3 / 24).
Proof.
  intros f f' a h M n. induction n as [| n IH]; intros pr Hh HM Hd Hlip.
  - (* empty range *)
    assert (Ez : a + INR 0 * h = a) by (simpl; ring).
    assert (pra : Riemann_integrable f a a).
    { apply continuity_implies_RiemannInt; [ apply Rle_refl | ].
      intros x Hx. apply (cont_of_deriv f f' a (a + INR 0 * h) Hd). lra. }
    rewrite (RI_endpoint f a (a + INR 0 * h) a pr pra Ez), (RiemannInt_P9 pra).
    simpl. replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - (* one more panel *)
    assert (HSn : INR (S n) = INR n + 1) by apply S_INR.
    assert (Hnh : 0 <= INR n * h)
      by (apply Rmult_le_pos; [ apply pos_INR | exact Hh ]).
    assert (Hgrow : a + INR n * h <= a + INR (S n) * h) by (rewrite HSn; nra).
    set (c := a + (INR n + / 2) * h).
    assert (Eb : c - h / 2 = a + INR n * h) by (unfold c; field).
    assert (Ec : c + h / 2 = a + INR (S n) * h) by (unfold c; rewrite HSn; field).
    (* the restricted hypotheses, for the induction hypothesis *)
    assert (Hd_n : forall y, a <= y <= a + INR n * h -> derivable_pt_lim f y (f' y))
      by (intros y Hy; apply Hd; lra).
    assert (Hlip_n : forall y z, a <= y <= a + INR n * h ->
                     a <= z <= a + INR n * h ->
                     Rabs (f' y - f' z) <= M * Rabs (y - z))
      by (intros y z Hy Hz; apply Hlip; lra).
    (* the three integrability proofs, regenerated from continuity *)
    assert (prn : Riemann_integrable f a (a + INR n * h)).
    { apply continuity_implies_RiemannInt; [ lra | ].
      intros x Hx. apply (cont_of_deriv f f' a (a + INR n * h) Hd_n); exact Hx. }
    assert (prn' : Riemann_integrable f a (c - h / 2)).
    { rewrite Eb. exact prn. }
    assert (prs : Riemann_integrable f (c - h / 2) (c + h / 2)).
    { apply continuity_implies_RiemannInt; [ lra | ].
      intros x Hx. apply (cont_of_deriv f f' a (a + INR (S n) * h) Hd). lra. }
    assert (pr' : Riemann_integrable f a (c + h / 2)).
    { rewrite Ec. exact pr. }
    (* additivity *)
    pose proof (RiemannInt_P26 prn' prs pr') as Hadd.
    assert (Esplit : RiemannInt pr = RiemannInt prn + RiemannInt prs).
    { rewrite (RI_endpoint f a (a + INR (S n) * h) (c + h / 2) pr pr'
                 (eq_sym Ec)).
      rewrite <- Hadd.
      rewrite (RI_endpoint f a (c - h / 2) (a + INR n * h) prn' prn Eb).
      reflexivity. }
    (* the single-panel bound *)
    assert (Hseg : Rabs (RiemannInt prs - 2 * (h / 2) * f c)
                   <= M * (h / 2) ^ 3 / 3).
    { apply (midpoint_single f f' c M (h / 2) prs); try lra.
      - intros y Hy. apply Hd. lra.
      - intros y z Hy Hz. apply Hlip; lra. }
    assert (Eseg : 2 * (h / 2) * f c = h * f c) by field.
    assert (Erate : M * (h / 2) ^ 3 / 3 = M * h ^ 3 / 24) by field.
    rewrite Eseg, Erate in Hseg.
    (* the induction hypothesis *)
    pose proof (IH prn Hh HM Hd_n Hlip_n) as HIH.
    (* glue *)
    cbn [msum]. fold c.
    rewrite Esplit.
    replace (RiemannInt prn + RiemannInt prs - (msum f a h n + h * f c))
      with ((RiemannInt prn - msum f a h n) + (RiemannInt prs - h * f c)) by ring.
    eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite HSn. nra.
Qed.

(* the form the quadrature consumes: n panels of width (b-a)/n.       *)
(* Stated with pr over [a,b] itself, NOT over a + n.(b-a)/n: those     *)
(* are equal as reals, but the second form leaves b - a inside pr's    *)
(* TYPE, where no caller can rewrite it away.                          *)
Corollary composite_midpoint_ab : forall (f f' : R -> R) (a b M : R) (n : nat)
  (pr : Riemann_integrable f a b),
  (0 < n)%nat -> a <= b -> 0 <= M ->
  (forall y, a <= y <= b -> derivable_pt_lim f y (f' y)) ->
  (forall y z, a <= y <= b -> a <= z <= b ->
     Rabs (f' y - f' z) <= M * Rabs (y - z)) ->
  Rabs (RiemannInt pr - msum f a ((b - a) / INR n) n)
  <= M * (b - a) ^ 3 / (24 * INR n ^ 2).
Proof.
  intros f f' a b M n pr Hn Hab HM Hd Hlip.
  assert (Hn0 : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hh : 0 <= (b - a) / INR n) by (apply Rle_mult_inv_pos; lra).
  assert (Etop : a + INR n * ((b - a) / INR n) = b) by (field; lra).
  assert (pr' : Riemann_integrable f a (a + INR n * ((b - a) / INR n)))
    by (rewrite Etop; exact pr).
  rewrite (RI_endpoint f a b (a + INR n * ((b - a) / INR n)) pr pr' (eq_sym Etop)).
  assert (Erate : INR n * (M * ((b - a) / INR n) ^ 3 / 24)
                = M * (b - a) ^ 3 / (24 * INR n ^ 2)) by (field; lra).
  rewrite <- Erate.
  apply (composite_midpoint f f' a ((b - a) / INR n) M n pr' Hh HM).
  - intros y Hy. apply Hd. rewrite Etop in Hy. exact Hy.
  - intros y z Hy Hz. rewrite Etop in Hy, Hz. apply Hlip; assumption.
Qed.

Print Assumptions composite_midpoint.
Print Assumptions composite_midpoint_ab.
