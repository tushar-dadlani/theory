(* ================================================================= *)
(*  ContinuousCoV.v  —  change of variables for a CONTINUOUS           *)
(*  integrand (no elementary antiderivative required).               *)
(*                                                                    *)
(*  The form the Gaussian squeeze needs.  Instead of a global C1_fun   *)
(*  antiderivative F (ChangeOfVariables), we use stdlib's LOCAL        *)
(*  `antiderivative` (differentiability only on [a,b], RiemannInt_P30) *)
(*  — sidestepping the global-C¹ wall.                                *)
(*                                                                    *)
(*    FTC_antideriv  : antiderivative f G a b (f continuous)           *)
(*                     ⇒ ∫_a^b f = G b − G a;                         *)
(*    cov_continuous : for g : C1_fun mapping [a,b] into [g a, g b]     *)
(*                     and f continuous on [g a, g b],                 *)
(*        ∫_a^b f(g t)·g'(t) dt  =  ∫_{g a}^{g b} f(u) du.             *)
(*                                                                    *)
(*  Proof of cov_continuous: Φ = primitive of f on [g a, g b]         *)
(*  (RiemannInt_P30); Φ∘g is a LOCAL antiderivative of (f∘g)·g' on     *)
(*  [a,b] (chain rule); FTC_antideriv on both sides gives              *)
(*  Φ(g b) − Φ(g a).  No global C1_fun of the primitive needed.        *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  FTC via a local antiderivative.                                  *)
(* ----------------------------------------------------------------- *)

Lemma FTC_antideriv : forall (f G : R -> R) (a b : R) (h : a <= b)
  (C0 : forall x, a <= x <= b -> continuity_pt f x)
  (pr : Riemann_integrable f a b),
  antiderivative f G a b -> RiemannInt pr = G b - G a.
Proof.
  intros f G a b h C0 pr Hanti.
  rewrite (RiemannInt_P20 h (FTC_P1 h C0) pr).
  destruct (antiderivative_Ucte f (primitive h (FTC_P1 h C0)) G a b
              (RiemannInt_P29 h C0) Hanti) as [C HC].
  assert (Hb : a <= b <= b) by lra.
  assert (Ha : a <= a <= b) by lra.
  rewrite (HC b Hb), (HC a Ha); ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Change of variables for a continuous integrand.                  *)
(* ----------------------------------------------------------------- *)

Theorem cov_continuous : forall (g : C1_fun) (f : R -> R) (a b : R),
  a <= b ->
  (forall t, a <= t <= b -> g a <= g t <= g b) ->
  (forall u, g a <= u <= g b -> continuity_pt f u) ->
  forall (prL : Riemann_integrable (fun t => f (g t) * derive g (diff0 g) t) a b)
         (prR : Riemann_integrable f (g a) (g b)),
  RiemannInt prL = RiemannInt prR.
Proof.
  intros g f a b Hab Hmap Hfcont prL prR.
  assert (Hbb : a <= b <= b) by lra.
  destruct (Hmap b Hbb) as [Hab' _].
  destruct (RiemannInt_P30 Hab' Hfcont) as [Phi HPhi].
  (* Φ∘g is a local antiderivative of (f∘g)·g' on [a,b] *)
  assert (Hcomp : antiderivative (fun t => f (g t) * derive g (diff0 g) t)
                    (fun t => Phi (g t)) a b).
  { split; [ | exact Hab ].
    intros t Ht.
    assert (Hgt : g a <= g t <= g b) by (apply Hmap; exact Ht).
    destruct HPhi as [HPhid _].
    destruct (HPhid (g t) Hgt) as [prPhi HprPhi].
    set (v := derive_pt Phi (g t) prPhi * derive g (diff0 g) t).
    assert (Hlim : derivable_pt_lim (fun s => Phi (g s)) t v).
    { unfold v; apply (derivable_pt_lim_comp g Phi t
                         (derive g (diff0 g) t) (derive_pt Phi (g t) prPhi)).
      - unfold derive, derive_pt; exact (proj2_sig (diff0 g t)).
      - unfold derive_pt; exact (proj2_sig prPhi). }
    exists (exist _ v Hlim); unfold v; rewrite HprPhi; reflexivity. }
  (* the L-integrand is continuous on [a,b] *)
  assert (Hcont : forall t, a <= t <= b ->
            continuity_pt (fun s => f (g s) * derive g (diff0 g) s) t).
  { intros t Ht; apply continuity_pt_mult.
    - apply (continuity_pt_comp g f t).
      + apply derivable_continuous_pt; exists (derive g (diff0 g) t).
        unfold derive, derive_pt; exact (proj2_sig (diff0 g t)).
      + apply Hfcont; apply Hmap; exact Ht.
    - apply (cont1 g). }
  rewrite (FTC_antideriv (fun s => f (g s) * derive g (diff0 g) s)
             (fun s => Phi (g s)) a b Hab Hcont prL Hcomp).
  rewrite (FTC_antideriv f Phi (g a) (g b) Hab' Hfcont prR HPhi).
  reflexivity.
Qed.

Print Assumptions FTC_antideriv.
Print Assumptions cov_continuous.

(* ================================================================= *)
(*  END ContinuousCoV.v                                              *)
(*  ∫_a^b f(g t)·g'(t) dt = ∫_{g a}^{g b} f(u) du for continuous f and *)
(*  monotone-into-range C¹ g — the substitution rule with no explicit  *)
(*  antiderivative, via the LOCAL `antiderivative` (no global C1_fun). *)
(*  This unlocks the Gaussian lower substitution                       *)
(*  ∫_0^√n (1−x²/n)ⁿ = √n·W_{2n+1}.                                    *)
(* ================================================================= *)
