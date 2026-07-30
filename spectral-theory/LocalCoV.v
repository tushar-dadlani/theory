(* ================================================================= *)
(*  LocalCoV.v  —  change of variables for a substitution g that is    *)
(*  differentiable only on [a,b] (no global C1_fun required).         *)
(*                                                                    *)
(*  cov_continuous (ContinuousCoV) demands g : C1_fun, i.e. g          *)
(*  differentiable EVERYWHERE.  The Gaussian UPPER flank needs         *)
(*  x = √n·tan θ, and tan is not globally differentiable (it blows up  *)
(*  at π/2).  cov_local drops the global requirement: g need only be   *)
(*  differentiable with continuous derivative g' ON [a,b].            *)
(*                                                                    *)
(*    cov_local : g differentiable on [a,b] with continuous g',        *)
(*        g monotone-into-range, f continuous on [g a, g b]  ⇒         *)
(*        ∫_a^b f(g t)·g'(t) dt = ∫_{g a}^{g b} f(u) du.               *)
(*                                                                    *)
(*  Same proof skeleton as cov_continuous (Φ = primitive of f, Φ∘g a   *)
(*  LOCAL antiderivative by the chain rule, FTC_antideriv both sides), *)
(*  but the derivative facts come from the pointwise hypotheses rather  *)
(*  than a C1_fun bundle.  No new axioms (classical Reals only).       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ContinuousCoV.
Open Scope R_scope.

Theorem cov_local : forall (g g' f : R -> R) (a b : R),
  a <= b ->
  (forall t, a <= t <= b -> derivable_pt_lim g t (g' t)) ->
  (forall t, a <= t <= b -> continuity_pt g' t) ->
  (forall t, a <= t <= b -> g a <= g t <= g b) ->
  (forall u, g a <= u <= g b -> continuity_pt f u) ->
  forall (prL : Riemann_integrable (fun t => f (g t) * g' t) a b)
         (prR : Riemann_integrable f (g a) (g b)),
  RiemannInt prL = RiemannInt prR.
Proof.
  intros g g' f a b Hab Hg' Hg'cont Hmap Hfcont prL prR.
  assert (Hbb : a <= b <= b) by lra.
  destruct (Hmap b Hbb) as [Hab' _].
  destruct (RiemannInt_P30 Hab' Hfcont) as [Phi HPhi].
  (* Φ∘g is a local antiderivative of (f∘g)·g' on [a,b] *)
  assert (Hcomp : antiderivative (fun t => f (g t) * g' t) (fun t => Phi (g t)) a b).
  { split; [ | exact Hab ]. intros t Ht.
    assert (Hgt : g a <= g t <= g b) by (apply Hmap; exact Ht).
    destruct HPhi as [HPhid _].
    destruct (HPhid (g t) Hgt) as [prPhi HprPhi].
    set (v := derive_pt Phi (g t) prPhi * g' t).
    assert (Hlim : derivable_pt_lim (fun s => Phi (g s)) t v).
    { unfold v; apply (derivable_pt_lim_comp g Phi t (g' t) (derive_pt Phi (g t) prPhi)).
      - exact (Hg' t Ht).
      - unfold derive_pt; exact (proj2_sig prPhi). }
    exists (exist _ v Hlim); unfold v; rewrite HprPhi; reflexivity. }
  (* the L-integrand is continuous on [a,b] *)
  assert (Hcont : forall t, a <= t <= b -> continuity_pt (fun s => f (g s) * g' s) t).
  { intros t Ht; apply continuity_pt_mult.
    - apply (continuity_pt_comp g f t).
      + apply derivable_continuous_pt; exists (g' t); exact (Hg' t Ht).
      + apply Hfcont; apply Hmap; exact Ht.
    - apply Hg'cont; exact Ht. }
  rewrite (FTC_antideriv (fun s => f (g s) * g' s) (fun s => Phi (g s)) a b Hab Hcont prL Hcomp).
  rewrite (FTC_antideriv f Phi (g a) (g b) Hab' Hfcont prR HPhi).
  reflexivity.
Qed.

Print Assumptions cov_local.

(* ================================================================= *)
(*  END LocalCoV.v                                                   *)
(*  ∫_a^b f(g t)·g'(t) dt = ∫_{g a}^{g b} f for g differentiable only   *)
(*  on [a,b] — the substitution rule freed from the global-C1_fun      *)
(*  wall, so x = √n·tan θ (the Gaussian upper flank) becomes usable.   *)
(* ================================================================= *)
