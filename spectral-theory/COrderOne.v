(* ================================================================= *)
(*  COrderOne.v  —  THE ORDER-1 STEP of Hadamard, stated precisely,    *)
(*  with everything proved except Borel-Caratheodory.                  *)
(*                                                                    *)
(*  After the zeros are divided out, H := xi / P is entire, zero-free  *)
(*  and of order 1, and Hadamard's last step concludes H = A . e^{bz}. *)
(*  Classically that splits four ways:                                 *)
(*                                                                    *)
(*    A  H entire zero-free  ==>  H = Cc . e^G, G entire               *)
(*    B  ln|H(z)| = ln|Cc| + Re G(z)  (growth on H  ->  bound on Re G) *)
(*    C  G' constant = b  ==>  G affine  ==>  H = A . e^{bz}           *)
(*    D  Re G <= M(R) with M(R) = o(R^2)  ==>  G' constant             *)
(*                                                                    *)
(*  A is already in the repo (CLogFExpEntire.logF_exp_entire); B and C  *)
(*  are proved here.  D -- Borel-Caratheodory -- is the ONLY new        *)
(*  analysis, and is isolated below as a single named Prop.            *)
(*                                                                    *)
(*    order_one_of_logderiv_const : the real content available today.  *)
(*      A zero-free entire function whose LOGARITHMIC DERIVATIVE       *)
(*      Hp/H is constant is exactly A . e^{bz}.                        *)
(*                                                                    *)
(*    order_one_step : BorelCaratheodory -> ... -> H = A . e^{bz}.     *)
(*                                                                    *)
(*  BorelCaratheodory is a Definition of type Prop and a HYPOTHESIS of *)
(*  order_one_step -- deliberately NOT an Axiom.  Nothing here is       *)
(*  assumed; the development's axiom set is untouched.                 *)
(*                                                                    *)
(*  WHY Mf IS REQUIRED MONOTONE.  D proves G'' w = 0 at a general centre  *)
(*  by applying the centre result to the translate Gw z := G (z + w),    *)
(*  which needs Re G (z+w) <= Mf (Cmod z + Cmod w) -- and that step is    *)
(*  exactly where monotonicity of Mf is used.  Without it D is NOT        *)
(*  provable as stated.  The cost is nil: order_one_step's own shifted    *)
(*  majorant Mf r - ln |Cc| is monotone whenever Mf is, and xi's          *)
(*  majorant from XiGrowthBound is increasing.                           *)
(*                                                                    *)
(*  WHY SubQuadLog AND NOT "order <= 1".  The hypothesis that actually  *)
(*  forces degree <= 1 is ln|H| = o(r^2), i.e. order < 2, and that is   *)
(*  what D consumes.  It is also exactly what xi supplies              *)
(*  (XiGrowthBound gives ln|xi| = O(r ln r), comfortably o(r^2)), so    *)
(*  phrasing it this way removes a conversion step rather than adding   *)
(*  one.  The majorant Mf is taken as existential DATA, since xi hands  *)
(*  over an explicit one.                                              *)
(*                                                                    *)
(*  THE INTENDED PROOF OF D, recorded so the follow-up is execution     *)
(*  rather than rediscovery.  For n >= 1,                               *)
(*      G^{(n)}(0)/n! = (1/(pi R^n)) INT_0^{2PI} Re G(R e^{i t}) e^{-i n t} dt, *)
(*  because the conjugate half contributes conj (INT G e^{i n t} dt) =  *)
(*  conj 0 = 0 by Cauchy (CPrimConv.pathint_loop_conv applied to        *)
(*  G(z) z^{n-1}).  Then M - Re G >= 0 together with the mean value     *)
(*  INT Re G = 2 PI Re G(0) (CCauchyFormula.meanval0) gives             *)
(*      |G^{(n)}(0)| <= 2 . n! . (M(R) - Re G(0)) / R^n.               *)
(*  At n = 2 the o(R^2) hypothesis sends the right side to 0, so        *)
(*  G''(0) = 0; the same at every centre gives G'' == 0, i.e. G'        *)
(*  constant.  The conjugate-integral identity that step needs is NOW   *)
(*  available -- CConjIntegral.Cintf_conj and, in the weighted form D    *)
(*  actually consumes, CConjIntegral.Cintf_conj_weighted(_zero).  So     *)
(*  every ingredient of D is now in the repo and what remains is the     *)
(*  assembly: the Cauchy-coefficient bookkeeping on arc R, the           *)
(*  positivity/ML estimate, and the n = 2 limit.                        *)
(*                                                                    *)
(*  NOT IN SCOPE HERE: D itself, and instantiating at xi -- the latter  *)
(*  is blocked upstream on the zero enumeration and the product, not    *)
(*  on this file.  Axiom-clean.                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCalculus
        CexpFull CexpfDeriv CSegInt CPrimConv CDerivConst CLogFExpEntire.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  small helpers                                                     *)
(* ----------------------------------------------------------------- *)
Lemma cmod_pos_ne : forall c, c <> C0 -> 0 < Cmod c.
Proof.
  intros c Hc. destruct (Cmod_nonneg c) as [Hlt | Heq]; [ exact Hlt | ].
  exfalso. apply Hc. apply (proj1 (Cmod0 c)). symmetry. exact Heq.
Qed.

Lemma is_Cderiv_val : forall F z d d', is_Cderiv F z d -> d = d' -> is_Cderiv F z d'.
Proof. intros F z d d' H E; subst; exact H. Qed.

Lemma Convex_all : Convex (fun _ : C => True).
Proof. intros a b _ _ s _; exact I. Qed.

Lemma Cderiv_lin : forall (b z : C), is_Cderiv (fun w => Cmul b w) z b.
Proof.
  intros b z.
  apply (is_Cderiv_val _ _ (Cadd (Cmul C0 z) (Cmul b C1))).
  - apply (Cderiv_mul (fun _ => b) (fun w => w) z C0 C1);
      [ apply Cderiv_const | apply Cderiv_id ].
  - ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  the growth predicate: ln |H| = o(r^2), i.e. order < 2             *)
(* ----------------------------------------------------------------- *)
Definition SubQuadLog (H : C -> C) : Prop :=
  exists Mf : R -> R,
    (forall r1 r2, r1 <= r2 -> Mf r1 <= Mf r2) /\
    (forall z, ln (Cmod (H z)) <= Mf (Cmod z)) /\
    (forall eps, 0 < eps -> exists R0, 0 < R0 /\
       forall r, R0 <= r -> Mf r <= eps * r ^ 2).

(* ----------------------------------------------------------------- *)
(*  A.  the entire logarithm, with a nonzero constant                 *)
(* ----------------------------------------------------------------- *)
Lemma zero_free_log_entire : forall (H Hp : C -> C),
  (forall z, is_Cderiv H z (Hp z)) ->
  (forall z, exists d, is_Cderiv Hp z d) ->
  (forall z, H z <> C0) ->
  CcontC (fun w => Cmul (Hp w) (Cinv (H w))) ->
  exists (G : C -> C) (Cc : C), Cc <> C0
    /\ (forall z, is_Cderiv G z (Cmul (Hp z) (Cinv (H z))))
    /\ (forall z, H z = Cmul Cc (Cexpf (G z))).
Proof.
  intros H Hp Hhol Hphol Hne0 Hcont.
  destruct (logF_exp_entire H Hp Hhol Hphol Hne0 Hcont) as [G [Cc [HG Hexp]]].
  exists G, Cc. split; [ | split; [ exact HG | exact Hexp ] ].
  intro HCc. apply (Hne0 C0). rewrite (Hexp C0), HCc. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the growth bound transfers to the real part of the logarithm  *)
(* ----------------------------------------------------------------- *)
Lemma log_mod_split : forall (H G : C -> C) (Cc : C), Cc <> C0 ->
  (forall z, H z = Cmul Cc (Cexpf (G z))) ->
  forall z, ln (Cmod (H z)) = ln (Cmod Cc) + Re (G z).
Proof.
  intros H G Cc HCc Hexp z.
  rewrite (Hexp z), Cmod_mul, Cmod_Cexpf.
  rewrite (ln_mult (Cmod Cc) (exp (Re (G z))) (cmod_pos_ne Cc HCc) (exp_pos _)).
  rewrite ln_exp. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  constant derivative  ==>  affine  ==>  H = A . e^{bz}         *)
(* ----------------------------------------------------------------- *)
Lemma affine_of_deriv_const : forall (G Gp : C -> C) (b : C),
  (forall z, is_Cderiv G z (Gp z)) ->
  (forall z, Gp z = b) ->
  forall z, G z = Cadd (G C0) (Cmul b z).
Proof.
  intros G Gp b HG Hb z.
  set (K := fun w => Cminus (G w) (Cmul b w)).
  assert (HK : forall w, is_Cderiv K w C0).
  { intro w. apply (is_Cderiv_val _ _ (Cminus (Gp w) b)).
    - apply (Cderiv_minus G (fun v => Cmul b v) w (Gp w) b);
        [ apply HG | apply Cderiv_lin ].
    - rewrite (Hb w). ring. }
  assert (Hconst : K z = K C0)
    by exact (Cderiv0_const (fun _ => True) Convex_all K
                (fun w _ => HK w) z C0 I I).
  unfold K in Hconst.
  assert (HK0 : Cminus (G C0) (Cmul b C0) = G C0) by ring.
  rewrite HK0 in Hconst.
  replace (G z) with (Cadd (Cminus (G z) (Cmul b z)) (Cmul b z)) by ring.
  rewrite Hconst. reflexivity.
Qed.

Theorem order_one_of_logderiv_const : forall (H Hp : C -> C) (b : C),
  (forall z, is_Cderiv H z (Hp z)) ->
  (forall z, exists d, is_Cderiv Hp z d) ->
  (forall z, H z <> C0) ->
  CcontC (fun w => Cmul (Hp w) (Cinv (H w))) ->
  (forall z, Cmul (Hp z) (Cinv (H z)) = b) ->
  exists A : C, A <> C0 /\ forall z, H z = Cmul A (Cexpf (Cmul b z)).
Proof.
  intros H Hp b Hhol Hphol Hne0 Hcont Hlog.
  destruct (zero_free_log_entire H Hp Hhol Hphol Hne0 Hcont)
    as [G [Cc [HCc [HG Hexp]]]].
  pose proof (affine_of_deriv_const G (fun z => Cmul (Hp z) (Cinv (H z))) b
                HG Hlog) as Haff.
  exists (Cmul Cc (Cexpf (G C0))). split.
  - apply Cmul_ne0; [ exact HCc | apply Cexpf_ne0 ].
  - intro z. rewrite (Hexp z), (Haff z), Cexpf_add. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the ONE missing analytic ingredient, as a named Prop           *)
(* ----------------------------------------------------------------- *)
Definition BorelCaratheodory : Prop :=
  forall (G Gp : C -> C) (Mf : R -> R),
    (forall z, is_Cderiv G z (Gp z)) ->
    (forall z, exists d, is_Cderiv Gp z d) ->
    (forall z, Re (G z) <= Mf (Cmod z)) ->
    (forall r1 r2, r1 <= r2 -> Mf r1 <= Mf r2) ->
    (forall eps, 0 < eps -> exists R0, 0 < R0 /\
       forall r, R0 <= r -> Mf r <= eps * r ^ 2) ->
    exists b, forall z, Gp z = b.

(* ----------------------------------------------------------------- *)
(*  THE ORDER-1 STEP, as a reduction to D                             *)
(* ----------------------------------------------------------------- *)
Theorem order_one_step : BorelCaratheodory ->
  forall (H Hp : C -> C),
    (forall z, is_Cderiv H z (Hp z)) ->
    (forall z, exists d, is_Cderiv Hp z d) ->
    (forall z, H z <> C0) ->
    CcontC (fun w => Cmul (Hp w) (Cinv (H w))) ->
    SubQuadLog H ->
    exists A b : C, A <> C0 /\ forall z, H z = Cmul A (Cexpf (Cmul b z)).
Proof.
  intros BC H Hp Hhol Hphol Hne0 Hcont [Mf [Hmono [Hbd Hsub]]].
  destruct (zero_free_log_entire H Hp Hhol Hphol Hne0 Hcont)
    as [G [Cc [HCc [HG Hexp]]]].
  set (Gp := fun z => Cmul (Hp z) (Cinv (H z))).
  (* Gp is holomorphic: it is Hp / H with H nonvanishing *)
  assert (HGp : forall z, exists d, is_Cderiv Gp z d).
  { intro z. destruct (Hphol z) as [dHp HdHp]. unfold Gp. eexists.
    apply Cderiv_div; [ exact HdHp | apply Hhol | apply Hne0 ]. }
  (* the growth bound moves to Re G, shifted by the constant -ln|Cc| *)
  set (Mf' := fun r => Mf r - ln (Cmod Cc)).
  assert (HReG : forall z, Re (G z) <= Mf' (Cmod z)).
  { intro z. unfold Mf'.
    pose proof (log_mod_split H G Cc HCc Hexp z) as Hsplit.
    pose proof (Hbd z) as Hz. lra. }
  (* the shift preserves monotonicity *)
  assert (Hmono' : forall r1 r2, r1 <= r2 -> Mf' r1 <= Mf' r2)
    by (intros r1 r2 H12; unfold Mf'; pose proof (Hmono r1 r2 H12); lra).
  (* and is still o(r^2): a constant is absorbed *)
  assert (Hsub' : forall eps, 0 < eps -> exists R0, 0 < R0 /\
             forall r, R0 <= r -> Mf' r <= eps * r ^ 2).
  { intros eps Heps.
    destruct (Hsub (eps / 2) ltac:(lra)) as [R0 [HR0 HR0b]].
    set (c := Rabs (ln (Cmod Cc))).
    assert (Hc0 : 0 <= c) by apply Rabs_pos.
    assert (Hneg : - ln (Cmod Cc) <= c)
      by (unfold c; rewrite <- Rabs_Ropp; apply Rle_abs).
    exists (Rmax (Rmax R0 1) (2 * c / eps + 1)). split.
    - apply Rlt_le_trans with R0; [ exact HR0 | ].
      apply Rle_trans with (Rmax R0 1); [ apply Rmax_l | apply Rmax_l ].
    - intros r Hr.
      assert (Hr0 : R0 <= r)
        by (apply Rle_trans with (Rmax R0 1);
            [ apply Rmax_l | apply Rle_trans with (Rmax (Rmax R0 1) (2*c/eps+1));
              [ apply Rmax_l | exact Hr ] ]).
      assert (Hr1 : 1 <= r)
        by (apply Rle_trans with (Rmax R0 1);
            [ apply Rmax_r | apply Rle_trans with (Rmax (Rmax R0 1) (2*c/eps+1));
              [ apply Rmax_l | exact Hr ] ]).
      assert (Hr2 : 2 * c / eps + 1 <= r)
        by (apply Rle_trans with (Rmax (Rmax R0 1) (2*c/eps+1));
            [ apply Rmax_r | exact Hr ]).
      (* r^2 >= r, so (eps/2) r^2 dominates the constant c *)
      assert (Hsq : r <= r ^ 2) by nra.
      assert (Hconst : c <= eps / 2 * r ^ 2).
      { apply Rle_trans with (eps / 2 * r); [ | nra ].
        apply (Rmult_le_reg_l (2 / eps)); [ apply Rdiv_lt_0_compat; lra | ].
        replace (2 / eps * (eps / 2 * r)) with r by (field; lra).
        replace (2 / eps * c) with (2 * c / eps) by (field; lra). lra. }
      pose proof (HR0b r Hr0) as Hm. unfold Mf'. lra. }
  destruct (BC G Gp Mf' HG HGp HReG Hmono' Hsub') as [b Hb].
  destruct (order_one_of_logderiv_const H Hp b Hhol Hphol Hne0 Hcont Hb)
    as [A [HA HAe]].
  exists A, b. split; [ exact HA | exact HAe ].
Qed.

Print Assumptions order_one_of_logderiv_const.
Print Assumptions order_one_step.
