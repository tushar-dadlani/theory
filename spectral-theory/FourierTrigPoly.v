(* ================================================================= *)
(*  FourierTrigPoly.v  —  Fourier F3, general trigonometric           *)
(*  polynomial: S_N f(x) → f(x) UNCONDITIONALLY for                   *)
(*                                                                    *)
(*     f(y) = c0 + Σ_{m=1}^{M} (a_m cos(m y) + b_m sin(m y)).         *)
(*                                                                    *)
(*  The localiser is LINEAR in f: the modal localisers gcosC/gsinC    *)
(*  (FourierMode) just add.  With                                     *)
(*     g(y) := Σ_{m=1}^{M} (a_m·Gcos m + b_m·Gsin m),                 *)
(*  a finite sum of GLOBAL C¹ functions (hence C¹), each modal factor *)
(*  satisfies Gcos m(y)·sin((x−y)/2) = cos(m y) − cos(m x) etc., so    *)
(*     g(y)·sin((x−y)/2)                                              *)
(*       = Σ_m [a_m(cos(m y)−cos(m x)) + b_m(sin(m y)−sin(m x))]       *)
(*       = f(y) − f(x)   (the constant c0 cancels).                   *)
(*  One application of FourierConverge.fourier_pointwise finishes it. *)
(*                                                                    *)
(*  No hypotheses beyond what is proved; no new axioms (classical     *)
(*  Reals only).                                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import DirichletKernel FourierRL FourierKernelRep FourierConverge
        FourierRsum FourierMode.
Open Scope R_scope.

Lemma Rsum_minus : forall (f g : nat -> R) n,
  Rsum (fun k => f k - g k) n = Rsum f n - Rsum g n.
Proof.
  intros f g n; induction n as [| n IH]; cbn [Rsum]; [ ring | rewrite IH; ring ].
Qed.

Section TrigPoly.

Variable x : R.
Variable c0 : R.
Variables a b : nat -> R.
Variable M : nat.

(* the localiser g and its derivative, termwise over the modes *)
Definition gterm  (m : nat) (t : R) : R := a m * Gcos  m x t + b m * Gsin  m x t.
Definition gterm' (m : nat) (t : R) : R := a m * Gcos' m x t + b m * Gsin' m x t.
Definition Gpoly  (t : R) : R := Rsum (fun m => gterm  m t) M.
Definition Gpoly' (t : R) : R := Rsum (fun m => gterm' m t) M.

Lemma gterm_deriv : forall m y, derivable_pt_lim (gterm m) y (gterm' m y).
Proof.
  intros m y; unfold gterm, gterm'.
  apply (derivable_pt_lim_plus (fun t => a m * Gcos m x t) (fun t => b m * Gsin m x t) y
           (a m * Gcos' m x y) (b m * Gsin' m x y)).
  - apply (derivable_pt_lim_scal (Gcos m x) (a m) y (Gcos' m x y)); apply Gcos_derivable.
  - apply (derivable_pt_lim_scal (Gsin m x) (b m) y (Gsin' m x y)); apply Gsin_derivable.
Qed.

Lemma gterm'_cont : forall m, continuity (gterm' m).
Proof.
  intros m z; unfold gterm'; apply continuity_pt_plus.
  - apply (continuity_pt_scal (Gcos' m x) (a m) z); apply Gcos'_cont.
  - apply (continuity_pt_scal (Gsin' m x) (b m) z); apply Gsin'_cont.
Qed.

Lemma Gpoly_derivable : forall y, derivable_pt_lim Gpoly y (Gpoly' y).
Proof.
  intro y; unfold Gpoly, Gpoly'.
  apply (Rsum_derivable gterm gterm' M y); intro m; apply gterm_deriv.
Qed.

Lemma Gpoly'_cont : continuity Gpoly'.
Proof. unfold Gpoly'; apply (Rsum_cont gterm' M); intro m; apply gterm'_cont. Qed.

Definition gpolyC : C1_fun :=
  mkC1 (c1 := Gpoly)
       (diff0 := fun t => exist _ (Gpoly' t) (Gpoly_derivable t))
       Gpoly'_cont.

Lemma gpolyC_val : forall y, gpolyC y = Gpoly y.
Proof. reflexivity. Qed.

(* the trigonometric polynomial f and its continuity *)
Definition fpoly (y : R) : R :=
  c0 + Rsum (fun m => a m * cos (INR m * y) + b m * sin (INR m * y)) M.

Lemma term_cont : forall m, continuity (fun t => a m * cos (INR m * t) + b m * sin (INR m * t)).
Proof.
  intros m z; apply continuity_pt_plus.
  - apply (continuity_pt_scal (fun t => cos (INR m * t)) (a m) z); apply cos_lam_cont.
  - apply (continuity_pt_scal (fun t => sin (INR m * t)) (b m) z); apply sin_lam_cont.
Qed.

Lemma fpoly_cont : continuity fpoly.
Proof.
  intro y; unfold fpoly; apply continuity_pt_plus.
  - apply continuity_pt_const; intros u v; reflexivity.
  - apply (Rsum_cont (fun m => fun t => a m * cos (INR m * t) + b m * sin (INR m * t)) M).
    intro m; apply term_cont.
Qed.

(* modal localiser identities, at the Gcos/Gsin level *)
Lemma Gcos_mult : forall m y, Gcos m x y * sin ((x - y) / 2) = cos (INR m * y) - cos (INR m * x).
Proof. intros m y; rewrite <- (gcosC_val m x y); apply Hg_cos_mode. Qed.
Lemma Gsin_mult : forall m y, Gsin m x y * sin ((x - y) / 2) = sin (INR m * y) - sin (INR m * x).
Proof. intros m y; rewrite <- (gsinC_val m x y); apply Hg_sin_mode. Qed.

(* per-mode: (a_m Gcos + b_m Gsin)·s = mode(y) − mode(x) *)
Lemma gterm_localises : forall m y,
  gterm m y * sin ((x - y) / 2)
  = (a m * cos (INR m * y) + b m * sin (INR m * y))
  - (a m * cos (INR m * x) + b m * sin (INR m * x)).
Proof.
  intros m y; unfold gterm.
  replace ((a m * Gcos m x y + b m * Gsin m x y) * sin ((x - y) / 2))
    with (a m * (Gcos m x y * sin ((x - y) / 2)) + b m * (Gsin m x y * sin ((x - y) / 2))) by ring.
  rewrite Gcos_mult, Gsin_mult; ring.
Qed.

Lemma Hg_poly : forall y, gpolyC y * sin ((x - y) / 2) = fpoly y - fpoly x.
Proof.
  intro y; rewrite gpolyC_val; unfold Gpoly.
  rewrite (Rsum_mult_r (fun m => gterm m y) (sin ((x - y) / 2)) M).
  rewrite (Rsum_ext_from1 (fun m => gterm m y * sin ((x - y) / 2))
             (fun m => (a m * cos (INR m * y) + b m * sin (INR m * y))
                     - (a m * cos (INR m * x) + b m * sin (INR m * x))) M
             (fun k => gterm_localises (S k) y)).
  rewrite Rsum_minus; unfold fpoly; ring.
Qed.

Theorem fourier_trig_poly : Un_cv (fun N => SN fpoly fpoly_cont N x) (fpoly x).
Proof. exact (fourier_pointwise fpoly fpoly_cont x gpolyC Hg_poly). Qed.

End TrigPoly.

Print Assumptions fourier_trig_poly.

(* ================================================================= *)
(*  END FourierTrigPoly.v                                            *)
(*  S_N f(x) → f(x) for every trigonometric polynomial f, every x,    *)
(*  unconditionally.  A dense, axiom-free class of the pointwise      *)
(*  convergence theorem.                                             *)
(* ================================================================= *)
