(* ================================================================= *)
(*  ZeroCounting.v                                                    *)
(*                                                                    *)
(*  Counting zeta zeros on the critical line from SIGN CHANGES of the  *)
(*  real boundary value  xir t = Re XiC(1/2 + it)  (the analogue of    *)
(*  the Riemann-Siegel Z-function).  This is the Turing / Sturm route: *)
(*  an intermediate-value argument turns each sign change of xir into  *)
(*  a genuine zero of Bxi, and disjoint sign-alternation gaps give a    *)
(*  lower bound on the number of zeros.                                *)
(*                                                                    *)
(*  KEY STEPS:                                                        *)
(*   - xir_continuity_pt: xir is continuous (from XiC holomorphic,      *)
(*     is_Cderiv_cont, bridged to real continuity_pt);                 *)
(*   - sign_change_zero_up/_down: opposite nonzero signs at a<b force   *)
(*     a zero STRICTLY inside (a,b)  (IVT_interv);                      *)
(*   - alternation_zeros: for a strictly increasing sample s_0<..<s_n   *)
(*     with signs alternating by parity, EACH gap (s_i,s_{i+1}) holds   *)
(*     a zero -- n disjoint gaps => at least n zeros;                   *)
(*   - two_zeros_from_alternation: the n=2 illustration, two DISTINCT   *)
(*     zeros.                                                          *)
(*                                                                    *)
(*  Each zero produced is a point where the Weyl phase Wxi reaches the  *)
(*  Dirichlet phase -1 (WeylFunction.zeros_are_Dirichlet_phase).        *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Ranalysis5.
Require Import ComplexField Cmodulus Holomorphic CHoloCalculus
        RiemannXiEntire CoherenceSingularity BerryKeatingDilation.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  Real continuity of xir from holomorphy of XiC                 *)
(* ----------------------------------------------------------------- *)

Lemma Cmod_Im_only : forall y, Cmod (mkC 0 y) = Rabs y.
Proof.
  intro y. unfold Cmod, Cnorm2; cbn [Re Im].
  replace (0 * 0 + y * y) with (Rsqr y) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

Lemma Re_le_Cmod : forall w, Rabs (Re w) <= Cmod w.
Proof.
  intro w. unfold Cmod. rewrite <- (sqrt_Rsqr_abs (Re w)).
  apply sqrt_le_1_alt. unfold Rsqr, Cnorm2.
  pose proof (Rle_0_sqr (Im w)) as H; unfold Rsqr in H; nra.
Qed.

Lemma Re_Cminus : forall a b, Re (Cminus a b) = Re a - Re b.
Proof. intros a b; unfold Cminus; reflexivity. Qed.

Lemma xir_continuity_pt : forall t0, continuity_pt (fun t => xir t) t0.
Proof.
  intro t0.
  destruct (XiC_entire (crit t0) I) as [d Hd].
  unfold continuity_pt, continue_in, limit1_in, limit_in; simpl.
  unfold R_dist. intros eps Heps.
  destruct (is_Cderiv_cont XiC (crit t0) d Hd eps Heps) as [del [Hdel Hcont]].
  exists del; split; [ exact Hdel | ].
  intros t [_ Hlt].
  set (h := mkC 0 (t - t0)).
  assert (Hh : Cmod h < del) by (unfold h; rewrite Cmod_Im_only; exact Hlt).
  specialize (Hcont h Hh).
  assert (Hc : Cadd (crit t0) h = crit t)
    by (unfold h, crit, Cadd; apply Ceq; cbn [Re Im]; ring).
  rewrite Hc in Hcont.
  unfold xir.
  eapply Rle_lt_trans; [ | exact Hcont ].
  rewrite <- Re_Cminus. apply Re_le_Cmod.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  A sign change forces a zero strictly inside                  *)
(* ----------------------------------------------------------------- *)

Lemma sign_change_zero_up : forall a b, a < b -> xir a < 0 -> 0 < xir b ->
  exists t, a < t < b /\ spec Bxi t.
Proof.
  intros a b Hab Ha Hb.
  destruct (IVT_interv (fun t => xir t) a b (fun x _ => xir_continuity_pt x) Hab Ha Hb)
    as [t [[Hle1 Hle2] Hz]].
  exists t; split.
  - split.
    + destruct Hle1 as [Hlt|Heq]; [ exact Hlt | rewrite <- Heq in Hz; lra ].
    + destruct Hle2 as [Hlt|Heq]; [ exact Hlt | rewrite Heq in Hz; lra ].
  - apply (proj2 (spec_Bxi_xir t)); exact Hz.
Qed.

Lemma sign_change_zero_down : forall a b, a < b -> 0 < xir a -> xir b < 0 ->
  exists t, a < t < b /\ spec Bxi t.
Proof.
  intros a b Hab Ha Hb.
  assert (Hcont : forall x, a <= x <= b -> continuity_pt (fun t => - xir t) x)
    by (intros x _; apply (continuity_pt_opp (fun t => xir t) x (xir_continuity_pt x))).
  assert (Ha' : (fun t => - xir t) a < 0) by (cbv beta; lra).
  assert (Hb' : 0 < (fun t => - xir t) b) by (cbv beta; lra).
  destruct (IVT_interv (fun t => - xir t) a b Hcont Hab Ha' Hb')
    as [t [[Hle1 Hle2] Hz]].
  assert (Hz0 : xir t = 0) by (cbv beta in Hz; lra).
  exists t; split.
  - split.
    + destruct Hle1 as [Hlt|Heq]; [ exact Hlt | rewrite <- Heq in Hz0; lra ].
    + destruct Hle2 as [Hlt|Heq]; [ exact Hlt | rewrite Heq in Hz0; lra ].
  - apply (proj2 (spec_Bxi_xir t)); exact Hz0.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Counting: n sign alternations => a zero in each of n gaps     *)
(* ----------------------------------------------------------------- *)

(* Signs alternate by parity: negative at even indices, positive odd.  *)
Definition alt_sign (s : nat -> R) (i : nat) : Prop :=
  if Nat.even i then xir (s i) < 0 else 0 < xir (s i).

Theorem alternation_zeros : forall (s : nat -> R) (n : nat),
  (forall i, (i < n)%nat -> s i < s (S i)) ->
  (forall i, (i <= n)%nat -> alt_sign s i) ->
  forall i, (i < n)%nat -> exists t, s i < t < s (S i) /\ spec Bxi t.
Proof.
  intros s n Hmono Hsign i Hi.
  assert (Hlt : s i < s (S i)) by (apply Hmono; exact Hi).
  pose proof (Hsign i (Nat.lt_le_incl _ _ Hi)) as HSi.
  pose proof (Hsign (S i) Hi) as HSSi.
  unfold alt_sign in HSi, HSSi.
  rewrite Nat.even_succ, <- Nat.negb_even in HSSi.
  destruct (Nat.even i) eqn:E.
  - (* i even: xir(s i) < 0, xir(s (S i)) > 0 *)
    cbn in HSSi. apply sign_change_zero_up; assumption.
  - (* i odd: xir(s i) > 0, xir(s (S i)) < 0 *)
    cbn in HSSi. apply sign_change_zero_down; assumption.
Qed.

(* The n = 2 illustration: two sign changes yield two DISTINCT zeros.   *)
Theorem two_zeros_from_alternation : forall a b c, a < b -> b < c ->
  xir a < 0 -> 0 < xir b -> xir c < 0 ->
  exists t1 t2, a < t1 < b /\ b < t2 < c /\ spec Bxi t1 /\ spec Bxi t2 /\ t1 < t2.
Proof.
  intros a b c Hab Hbc Ha Hb Hc.
  destruct (sign_change_zero_up a b Hab Ha Hb) as [t1 [Ht1 Hs1]].
  destruct (sign_change_zero_down b c Hbc Hb Hc) as [t2 [Ht2 Hs2]].
  exists t1, t2.
  destruct Ht1 as [Ht1a Ht1b]; destruct Ht2 as [Ht2a Ht2b].
  repeat split; try assumption; lra.
Qed.

(* The mirrored companion.  two_zeros_from_alternation wants (-,+,-);   *)
(* the verified facts for the first two zeros are xir 10 > 0,            *)
(* xir 16 < 0, xir 22 > 0, i.e. (+,-,+).  Same two IVT calls, swapped.   *)
Theorem two_zeros_from_alternation' : forall a b c, a < b -> b < c ->
  0 < xir a -> xir b < 0 -> 0 < xir c ->
  exists t1 t2, a < t1 < b /\ b < t2 < c /\ spec Bxi t1 /\ spec Bxi t2 /\ t1 < t2.
Proof.
  intros a b c Hab Hbc Ha Hb Hc.
  destruct (sign_change_zero_down a b Hab Ha Hb) as [t1 [Ht1 Hs1]].
  destruct (sign_change_zero_up b c Hbc Hb Hc) as [t2 [Ht2 Hs2]].
  exists t1, t2.
  destruct Ht1 as [Ht1a Ht1b]; destruct Ht2 as [Ht2a Ht2b].
  repeat split; try assumption; lra.
Qed.

Print Assumptions two_zeros_from_alternation'.
Print Assumptions xir_continuity_pt.
Print Assumptions alternation_zeros.
Print Assumptions two_zeros_from_alternation.
