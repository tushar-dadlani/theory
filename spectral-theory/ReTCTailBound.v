(* ================================================================= *)
(*  ReTCTailBound.v  —  Stage 2 capstone: the concrete tail bound.       *)
(*                                                                    *)
(*  The truncation error of the oscillatory integral                    *)
(*     Re TC(1/2+it) = int_1^inf Psi(u) u^{-3/4} cos((t/2) ln u) du      *)
(*  at cutoff X has the CLOSED-FORM exponential bound                    *)
(*                                                                    *)
(*    ReTC_tail_bound : 1 <= X ->                                       *)
(*      Rabs (Re TC(1/2+it) - int_1^X Re(wkerC(1/2+it) .))              *)
(*        <= Cc . e^{-pi X} / pi,    Cc = 1/(1 - e^{-pi}) (~ 1.0451).    *)
(*                                                                    *)
(*  Chain: |Re(wkerC(1/2+it) u)| <= Cmod(wkerC(1/2+it) u) = wker(1/2) u  *)
(*  = u^{-3/4} Psi(u) <= Psi(u) <= Cc e^{-pi u} (Psi_upper1); then        *)
(*  improper_tail_le against Cc . edk (edk_improper), whose tail is       *)
(*  Cc e^{-pi X}/pi.  At X = 4 this is ~ 1.2e-6 -- negligible against the *)
(*  ~1e-3 margins of the sign change.  Axiom-clean.                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField ThetaTailEntire CoherenceSingularity MellinTail
        MellinElem RiemannPsi ThetaTailBounds ExpTailIntegral MellinTailBound
        CImproperIntegral ImproperCv1.
Open Scope R_scope.

Definition Cc : R := / (1 - exp (- PI)).

Theorem ReTC_tail_bound : forall t X, 1 <= X ->
  Rabs (Re (TC (crit t))
        - pint1 (fun u => Re (wkerC (crit t) u)) (cont_RI _ (cont_wkerC_re (crit t))) X)
  <= Cc * exp (- (PI * X)) / PI.
Proof.
  intros t X HX. pose proof PI_RGT_0 as HPI.
  set (Hf := cont_RI _ (cont_wkerC_re (crit t))).
  set (gdom := fun u => Cc * edk u).
  set (gdom_int := fun x y => RI_scal edk Cc x y (edk_int x y)).
  assert (HI : ImproperCv1 (fun u => Re (wkerC (crit t) u)) Hf (Re (TC (crit t))))
    by (destruct (TC_spec (crit t)) as [HRe _]; exact HRe).
  assert (HJ : ImproperCv1 gdom gdom_int (Cc * (exp (- PI) / PI)))
    by (apply (improper_scal edk Cc edk_int gdom_int (exp (- PI) / PI)); apply edk_improper).
  assert (Hdom : forall u, 1 <= u -> Rabs (Re (wkerC (crit t) u)) <= gdom u).
  { intros u Hu. eapply Rle_trans; [ apply Cmod_Re | ].
    rewrite Cmod_wkerC.
    assert (HRe2 : Re (crit t) = / 2) by (unfold crit; reflexivity).
    rewrite HRe2. unfold gdom, edk, wker. rewrite (clamp_id u Hu).
    apply Rle_trans with (1 * Psi u).
    - apply Rmult_le_compat_r; [ apply Psi_nonneg | ].
      unfold Rpower.
      assert (Hln : 0 <= ln u).
      { destruct Hu as [Hlt | Heq];
          [ rewrite <- ln_1; apply Rlt_le, ln_increasing; lra
          | subst; rewrite ln_1; lra ]. }
      apply Rle_trans with (exp 0);
        [ apply exp_le_mono; nra | rewrite exp_0; lra ].
    - rewrite Rmult_1_l.
      replace (Cc * exp (- (PI * u))) with (exp (- (PI * u)) / (1 - exp (- PI)))
        by (unfold Cc, Rdiv; ring).
      apply Psi_upper1; exact Hu. }
  pose proof (improper_tail_le (fun u => Re (wkerC (crit t) u)) Hf gdom gdom_int
                (Re (TC (crit t))) (Cc * (exp (- PI) / PI)) X HI HJ Hdom HX) as Hbound.
  assert (Hpint : pint1 gdom gdom_int X = Cc * pint1 edk edk_int X)
    by (unfold pint1, gdom_int;
        apply (RiemannInt_scal1 edk Cc X (edk_int 1 X)
                 (RI_scal edk Cc 1 X (edk_int 1 X)) HX)).
  rewrite Hpint, (edk_pint X HX) in Hbound.
  replace (Cc * (exp (- PI) / PI)
           - Cc * (- / PI * exp (- (PI * X)) - - / PI * exp (- (PI * 1))))
    with (Cc * exp (- (PI * X)) / PI) in Hbound
    by (rewrite Rmult_1_r; field; lra).
  exact Hbound.
Qed.

Print Assumptions ReTC_tail_bound.
