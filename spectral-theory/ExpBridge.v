(* ================================================================= *)
(*  ExpBridge.v  —  Newman A3: the u = e^t change of variables.          *)
(*                                                                    *)
(*  The Newman Laplace transform lives in t-space (int_0^oo ... e^{-zt}), *)
(*  the Phi cell representation in u-space (int_1^oo ... u^{-s-1}).  This  *)
(*  file is the analytic bridge between them:                            *)
(*                                                                    *)
(*    Cintf_exp_cov : int_a^b F(e^t) e^t dt = int_{e^a}^{e^b} F(u) du,     *)
(*                                                                    *)
(*  the complex change of variables u = e^t (du = e^t dt), obtained by     *)
(*  applying the real cov_local componentwise (Re and Im).  Instantiated   *)
(*  to the cell endpoints (cell_cov) it maps the t-space cell              *)
(*  [ln(k+1), ln(k+2)] to the u-space cell [k+1, k+2].  Axiom-clean.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt ContinuousCoV LocalCoV.
Open Scope R_scope.

Lemma cont_exp : forall x, continuity_pt exp x.
Proof. intro x; apply derivable_continuous_pt; exists (exp x); apply derivable_pt_lim_exp. Qed.

Lemma exp_mono_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b Hab; destruct (Rle_lt_or_eq_dec a b Hab) as [H | H];
    [ left; apply exp_increasing; exact H | subst; apply Rle_refl ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the complex change of variables  u = e^t                           *)
(* ----------------------------------------------------------------- *)

Lemma Cintf_exp_cov : forall (F : R -> C) (HFc : Ccont F) a b
  (Hc : Ccont (fun t => Cmul (F (exp t)) (RtoC (exp t)))),
  a <= b ->
  Cintf (fun t => Cmul (F (exp t)) (RtoC (exp t))) Hc a b = Cintf F HFc (exp a) (exp b).
Proof.
  intros F HFc a b Hc Hab.
  assert (Hexpab : exp a <= exp b) by (apply exp_mono_le; exact Hab).
  apply Ceq.
  - rewrite !Re_Cintf.
    assert (prLc : Riemann_integrable (fun t => Re (F (exp t)) * exp t) a b).
    { apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_mult;
        [ apply (continuity_pt_comp exp (fun u => Re (F u))); [ apply cont_exp | apply (proj1 HFc) ]
        | apply cont_exp ] ]. }
    assert (prRc : Riemann_integrable (fun u => Re (F u)) (exp a) (exp b))
      by (apply continuity_implies_RiemannInt; [ exact Hexpab | intros u _; apply (proj1 HFc) ]).
    transitivity (RiemannInt prLc).
    + apply RiemannInt_P18; [ exact Hab | intros x _; unfold Cmul, RtoC; cbn [Re Im]; ring ].
    + transitivity (RiemannInt prRc); [ | apply RiemannInt_P5 ].
      apply (cov_local exp exp (fun u => Re (F u)) a b Hab
               (fun t _ => derivable_pt_lim_exp t) (fun t _ => cont_exp t)
               (fun t Ht => conj (exp_mono_le a t (proj1 Ht)) (exp_mono_le t b (proj2 Ht)))
               (fun u _ => proj1 HFc u)).
  - rewrite !Im_Cintf.
    assert (prLc : Riemann_integrable (fun t => Im (F (exp t)) * exp t) a b).
    { apply continuity_implies_RiemannInt; [ exact Hab | intros x _; apply continuity_pt_mult;
        [ apply (continuity_pt_comp exp (fun u => Im (F u))); [ apply cont_exp | apply (proj2 HFc) ]
        | apply cont_exp ] ]. }
    assert (prRc : Riemann_integrable (fun u => Im (F u)) (exp a) (exp b))
      by (apply continuity_implies_RiemannInt; [ exact Hexpab | intros u _; apply (proj2 HFc) ]).
    transitivity (RiemannInt prLc).
    + apply RiemannInt_P18; [ exact Hab | intros x _; unfold Cmul, RtoC; cbn [Re Im]; ring ].
    + transitivity (RiemannInt prRc); [ | apply RiemannInt_P5 ].
      apply (cov_local exp exp (fun u => Im (F u)) a b Hab
               (fun t _ => derivable_pt_lim_exp t) (fun t _ => cont_exp t)
               (fun t Ht => conj (exp_mono_le a t (proj1 Ht)) (exp_mono_le t b (proj2 Ht)))
               (fun u _ => proj2 HFc u)).
Qed.

(* ----------------------------------------------------------------- *)
(*  the cell instantiation: t-cell [ln(k+1), ln(k+2)] -> u-cell [k+1,k+2] *)
(* ----------------------------------------------------------------- *)

Lemma cell_cov : forall (F : R -> C) (HFc : Ccont F) (k : nat)
  (Hc : Ccont (fun t => Cmul (F (exp t)) (RtoC (exp t)))),
  Cintf (fun t => Cmul (F (exp t)) (RtoC (exp t)))
        Hc (ln (INR (S k))) (ln (INR (S (S k))))
  = Cintf F HFc (INR (S k)) (INR (S (S k))).
Proof.
  intros F HFc k Hc.
  assert (Hle : ln (INR (S k)) <= ln (INR (S (S k))))
    by (apply Rlt_le, ln_increasing; [ apply lt_0_INR; lia | apply lt_INR; lia ]).
  rewrite (Cintf_exp_cov F HFc (ln (INR (S k))) (ln (INR (S (S k)))) Hc Hle).
  rewrite !exp_ln by (apply lt_0_INR; lia); reflexivity.
Qed.

Print Assumptions Cintf_exp_cov.
Print Assumptions cell_cov.

(* ================================================================= *)
(*  END ExpBridge.v — the u = e^t complex change of variables.           *)
(*  With F(u) = u^{-(z+2)} the t-integrand F(e^t)e^t = e^{-(z+1)t}, so     *)
(*  int_{ln N}^{ln(N+1)} e^{-(z+1)t} dt = int_N^{N+1} u^{-(z+2)} du -- the  *)
(*  cell that links the Newman Laplace kernel to the Phi u-power kernel.   *)
(* ================================================================= *)
