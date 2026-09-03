(* ================================================================= *)
(*  CPolarPath.v  --  the log-derivative integral IS the phase change. *)
(*                                                                    *)
(*    F(gam u) = exp(Lg u) . (cos (ph u), sin (ph u))                  *)
(*      ==>  the path integral of Fd/F along gam over [a,b]            *)
(*             = (Lg b - Lg a) + i . (ph b - ph a).                    *)
(*                                                                    *)
(*  This is the missing half of the counting argument.  CArgPrinciple  *)
(*  Rect.arg_principle_rect turns counting zeros into evaluating a     *)
(*  contour integral; this turns that integral into a PHASE CHANGE,    *)
(*  which is a real number one can bound by sampling.  Round a closed  *)
(*  loop the modulus part cancels and                                  *)
(*                                                                    *)
(*      2*pi*i*n  =  i * (total phase change),   n = Delta(ph)/2*pi.   *)
(*                                                                    *)
(*  There is deliberately NO complex logarithm here, and no branch     *)
(*  choice.  ph is supplied by the caller as an honest real function   *)
(*  with an honest derivative -- exactly the shape CPolarDir.PosDir    *)
(*  and GammaDir.Pang already produce for Gamma, and which composes    *)
(*  multiplicatively over xi's four factors.  The repo's refusal to    *)
(*  introduce Clog/Carg (CPolarDir.v:4) costs nothing here.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CIntegral2 CSegInt
        CPathIntegral CPathFTC ContinuousCoV.
Open Scope R_scope.

Section PolarPath.

Variables (F Fd : C -> C) (gam gam' : R -> C) (Lg ph Ld phd : R -> R).

Hypothesis HgR : forall u, derivable_pt_lim (fun s => Re (gam s)) u (Re (gam' u)).
Hypothesis HgI : forall u, derivable_pt_lim (fun s => Im (gam s)) u (Im (gam' u)).
Hypothesis HF  : forall u, is_Cderiv F (gam u) (Fd (gam u)).
Hypothesis HL  : forall u, derivable_pt_lim Lg u (Ld u).
Hypothesis Hp  : forall u, derivable_pt_lim ph u (phd u).
Hypothesis Hre : forall u, Re (F (gam u)) = exp (Lg u) * cos (ph u).
Hypothesis Him : forall u, Im (F (gam u)) = exp (Lg u) * sin (ph u).

(* ---- the two component derivatives, from the polar form ---- *)

Lemma polar_Re_deriv : forall u,
  derivable_pt_lim (fun s => Re (F (gam s))) u
    (exp (Lg u) * Ld u * cos (ph u) + exp (Lg u) * (- sin (ph u) * phd u)).
Proof.
  intro u.
  assert (Heq : (fun s => Re (F (gam s))) = (fun s => exp (Lg s) * cos (ph s)))
    by (apply functional_extensionality; intro s; apply Hre).
  rewrite Heq.
  apply (derivable_pt_lim_mult (fun s => exp (Lg s)) (fun s => cos (ph s)) u
           (exp (Lg u) * Ld u) (- sin (ph u) * phd u)).
  - apply (derivable_pt_lim_comp Lg exp u (Ld u) (exp (Lg u)));
      [ apply HL | apply derivable_pt_lim_exp ].
  - apply (derivable_pt_lim_comp ph cos u (phd u) (- sin (ph u)));
      [ apply Hp | apply derivable_pt_lim_cos ].
Qed.

Lemma polar_Im_deriv : forall u,
  derivable_pt_lim (fun s => Im (F (gam s))) u
    (exp (Lg u) * Ld u * sin (ph u) + exp (Lg u) * (cos (ph u) * phd u)).
Proof.
  intro u.
  assert (Heq : (fun s => Im (F (gam s))) = (fun s => exp (Lg s) * sin (ph s)))
    by (apply functional_extensionality; intro s; apply Him).
  rewrite Heq.
  apply (derivable_pt_lim_mult (fun s => exp (Lg s)) (fun s => sin (ph s)) u
           (exp (Lg u) * Ld u) (cos (ph u) * phd u)).
  - apply (derivable_pt_lim_comp Lg exp u (Ld u) (exp (Lg u)));
      [ apply HL | apply derivable_pt_lim_exp ].
  - apply (derivable_pt_lim_comp ph sin u (phd u) (cos (ph u)));
      [ apply Hp | apply derivable_pt_lim_sin ].
Qed.

(* ---- the chain rule pins Re/Im of F' . gam' ---- *)

Lemma chain_Re : forall u,
  Re (Cmul (Fd (gam u)) (gam' u))
  = exp (Lg u) * Ld u * cos (ph u) + exp (Lg u) * (- sin (ph u) * phd u).
Proof.
  intro u.
  apply (uniqueness_limite (fun s => Re (F (gam s))) u);
    [ apply (Cderiv_path_Re F gam gam' u (Fd (gam u)) (HF u) (HgR u) (HgI u))
    | apply polar_Re_deriv ].
Qed.

Lemma chain_Im : forall u,
  Im (Cmul (Fd (gam u)) (gam' u))
  = exp (Lg u) * Ld u * sin (ph u) + exp (Lg u) * (cos (ph u) * phd u).
Proof.
  intro u.
  apply (uniqueness_limite (fun s => Im (F (gam s))) u);
    [ apply (Cderiv_path_Im F gam gam' u (Fd (gam u)) (HF u) (HgR u) (HgI u))
    | apply polar_Im_deriv ].
Qed.

(* ---- the integrand collapses to (Ld, phd) ---- *)

Lemma quot_polar : forall (W V : C) (e Lc pc c s : R),
  0 < e -> c * c + s * s = 1 ->
  Re W = e * Lc * c + e * (- s * pc) ->
  Im W = e * Lc * s + e * (c * pc) ->
  Re V = e * c -> Im V = e * s ->
  Cmul W (Cinv V) = mkC Lc pc.
Proof.
  intros W V e Lc pc c s He Hsc HWr HWi HVr HVi.
  assert (Hd : e * c * (e * c) + e * s * (e * s) > 0) by nra.
  unfold Cmul, Cinv, Cnorm2; apply Ceq; cbn [Re Im];
    rewrite HWr, HWi, HVr, HVi; field; apply Rgt_not_eq; exact Hd.
Qed.

Lemma integrand_polar : forall u,
  Cmul (Cmul (Fd (gam u)) (Cinv (F (gam u)))) (gam' u) = mkC (Ld u) (phd u).
Proof.
  intro u.
  assert (Hsplit : Cmul (Cmul (Fd (gam u)) (Cinv (F (gam u)))) (gam' u)
                 = Cmul (Cmul (Fd (gam u)) (gam' u)) (Cinv (F (gam u)))) by ring.
  rewrite Hsplit.
  apply (quot_polar _ _ (exp (Lg u)) (Ld u) (phd u) (cos (ph u)) (sin (ph u)));
    [ apply exp_pos
    | pose proof (sin2_cos2 (ph u)); unfold Rsqr in *; lra
    | apply chain_Re | apply chain_Im | apply Hre | apply Him ].
Qed.

(* ================================================================= *)
(*  THE BRIDGE.                                                        *)
(* ================================================================= *)

Theorem pathint_logderiv_phase : forall (a b : R) (Hab : a <= b)
  (Hf : Ccont (fun u => Cmul (Cmul (Fd (gam u)) (Cinv (F (gam u)))) (gam' u))),
  pathint gam gam' (fun z => Cmul (Fd z) (Cinv (F z))) Hf a b
  = mkC (Lg b - Lg a) (ph b - ph a).
Proof.
  intros a b Hab Hf; unfold pathint, Cintf; apply Ceq; cbn [Re Im].
  - apply (FTC_antideriv _ Lg a b Hab (fun x _ => proj1 Hf x)).
    split; [ | exact Hab ]; intros x _.
    exists (exist (fun l => derivable_pt_lim Lg x l) (Ld x) (HL x)).
    unfold derive_pt; cbn [proj1_sig]; cbv beta.
    rewrite (integrand_polar x); reflexivity.
  - apply (FTC_antideriv _ ph a b Hab (fun x _ => proj2 Hf x)).
    split; [ | exact Hab ]; intros x _.
    exists (exist (fun l => derivable_pt_lim ph x l) (phd x) (Hp x)).
    unfold derive_pt; cbn [proj1_sig]; cbv beta.
    rewrite (integrand_polar x); reflexivity.
Qed.

End PolarPath.

(* ================================================================= *)
(*  What the two halves say together.  Stage 1 gives the left side of  *)
(*  the first hypothesis, this file the four right sides; the total    *)
(*  phase change round the contour is 2*pi*n, and the log-moduli       *)
(*  telescope to 0 as a CONSEQUENCE rather than an assumption.         *)
(* ================================================================= *)

Theorem count_eq_phase : forall (n : nat) (r1 r2 r3 r4 d1 d2 d3 d4 : R),
  Cadd (mkC r1 d1) (Cadd (mkC r2 d2) (Cadd (mkC r3 d3) (mkC r4 d4)))
    = Cmul (RtoC (INR n)) (mkC 0 (2 * PI)) ->
  d1 + d2 + d3 + d4 = 2 * PI * INR n /\ r1 + r2 + r3 + r4 = 0.
Proof.
  intros n r1 r2 r3 r4 d1 d2 d3 d4 H.
  assert (HR := f_equal Re H); assert (HI := f_equal Im H).
  unfold Cadd, Cmul, RtoC in HR, HI; cbn [Re Im] in HR, HI.
  split; lra.
Qed.

Print Assumptions pathint_logderiv_phase.
Print Assumptions count_eq_phase.

(* ================================================================= *)
(*  END CPolarPath.v -- the contour integral of F'/F is the phase      *)
(*  change, so an integer zero count becomes a real number to bound.   *)
(* ================================================================= *)
