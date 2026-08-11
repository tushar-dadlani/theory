(* ================================================================= *)
(*  NewmanBlock.v  —  Newman A3: the Tauberian block integral.           *)
(*                                                                    *)
(*    block_int :  int_a^{lam a} (lam a - t)/t^2 dt  =  lam - 1 - ln lam,   *)
(*                                                                    *)
(*  the exact value of the monotonicity "block" (FTC on the antiderivative *)
(*  -lam a/t - ln t).  With gap_pos (NewmanTauber) its value is a fixed     *)
(*  POSITIVE constant for lam != 1 -- the quantitative contradiction         *)
(*  driving Newman's Tauberian squeeze.  Axiom-clean.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV NewmanTauber.
Open Scope R_scope.

Lemma div_const_deriv : forall c t, t <> 0 ->
  derivable_pt_lim (fun u => c / u) t (- c / (t * t)).
Proof.
  intros c t Ht.
  assert (Hd : derivable_pt_lim (fun u => c / u) t ((0 * t - 1 * c) / (t * t))).
  { pose proof (derivable_pt_lim_div (fun _ => c) (fun u => u) t 0 1
                  (derivable_pt_lim_const c t) (derivable_pt_lim_id t) Ht) as H.
    unfold Rsqr in H; exact H. }
  replace (- c / (t * t)) with ((0 * t - 1 * c) / (t * t)) by (field; exact Ht); exact Hd.
Qed.

Lemma cont_id : forall x, continuity_pt (fun u => u) x.
Proof. intro x; apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id. Qed.

Lemma block_cont : forall a lam x, 0 < x ->
  continuity_pt (fun t => (lam * a - t) / (t * t)) x.
Proof.
  intros a lam x Hx; apply continuity_pt_div.
  - apply continuity_pt_minus;
      [ apply continuity_pt_const; intros u v; reflexivity | apply cont_id ].
  - apply continuity_pt_mult; apply cont_id.
  - assert (0 < x * x) by nra; lra.
Qed.

Lemma block_int : forall a lam (Ha : 0 < a) (Hlam : 1 <= lam)
  (pr : Riemann_integrable (fun t => (lam * a - t) / (t * t)) a (lam * a)),
  RiemannInt pr = lam - 1 - ln lam.
Proof.
  intros a lam Ha Hlam pr.
  assert (Hlam0 : 0 < lam) by lra.
  assert (Hab : a <= lam * a) by nra.
  assert (Hanti : antiderivative (fun t => (lam * a - t) / (t * t))
                    (fun u => - (lam * a) / u - ln u) a (lam * a)).
  { split; [ | exact Hab ]; intros x [Hx1 Hx2]; assert (Hxpos : 0 < x) by lra.
    assert (HGd : derivable_pt_lim (fun u => - (lam * a) / u - ln u) x
                    ((lam * a - x) / (x * x))).
    { replace ((lam * a - x) / (x * x)) with (- (- (lam * a)) / (x * x) - / x)
        by (field; lra).
      apply derivable_pt_lim_minus;
        [ apply (div_const_deriv (- (lam * a)) x); lra
        | apply derivable_pt_lim_ln; exact Hxpos ]. }
    exists (exist _ ((lam * a - x) / (x * x)) HGd); unfold derive_pt; simpl; reflexivity. }
  rewrite (FTC_antideriv (fun t => (lam * a - t) / (t * t)) (fun u => - (lam * a) / u - ln u)
             a (lam * a) Hab (fun x Hx => block_cont a lam x ltac:(lra)) pr Hanti).
  rewrite (ln_mult lam a Hlam0 Ha).
  replace (- (lam * a) / (lam * a)) with (-1) by (field; nra).
  replace (- (lam * a) / a) with (- lam) by (field; lra).
  lra.
Qed.

Print Assumptions block_int.

(* ================================================================= *)
(*  END NewmanBlock.v — the block value lam - 1 - ln lam.                  *)
(*  block_int + gap_pos give the fixed positive gain; the remaining         *)
(*  Tauberian squeeze wires this monotonicity contradiction against the     *)
(*  Cauchy tail (from the contour conclusion) to Un_cv (psi N/INR N) 1.     *)
(* ================================================================= *)
