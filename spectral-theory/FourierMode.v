(* ================================================================= *)
(*  FourierMode.v  —  unconditional pointwise convergence for a       *)
(*  general Fourier mode:  S_N cos(m·)(x) → cos(mx),                  *)
(*                         S_N sin(m·)(x) → sin(mx),  every m, x.     *)
(*                                                                    *)
(*  The localiser for cos(m·) is built from a TELESCOPING sum.  With  *)
(*     φ(k) := k·y + (m−k)·x,   mid(k) := (φ(k)+φ(k−1))/2,            *)
(*     cos(m y) − cos(m x) = Σ_{k=1}^{m} [cos φ(k) − cos φ(k−1)]       *)
(*                         = Σ_{k=1}^{m} 2 sin(mid k)·sin((x−y)/2),   *)
(*  since φ(k)−φ(k−1) = y−x and cos A − cos B = 2 sin((A+B)/2) sin(   *)
(*  (B−A)/2).  So g(y) := Σ_{k=1}^{m} 2 sin(mid k) is a GLOBAL C¹      *)
(*  function (finite sum of sines of affine args, NO singularity)     *)
(*  with g(y)·sin((x−y)/2) = cos(m y) − cos(m x) for all y.  The sine *)
(*  mode is identical with 2 cos(mid k) and cos A − cos B ↦ sin A −    *)
(*  sin B.                                                            *)
(*                                                                    *)
(*  Discharges FourierConverge.fourier_pointwise for f = cos(m·),     *)
(*  sin(m·) with no hypotheses.  No new axioms (classical Reals).     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import DirichletKernel FourierRL FourierKernelRep FourierConverge FourierRsum.
Open Scope R_scope.

(* product-to-sum atoms *)
Lemma two_sin_sin : forall A B, 2 * sin A * sin B = cos (A - B) - cos (A + B).
Proof. intros A B; rewrite cos_minus, cos_plus; ring. Qed.
Lemma two_cos_sin : forall A B, 2 * cos A * sin B = sin (A + B) - sin (A - B).
Proof. intros A B; rewrite sin_plus, sin_minus; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  The affine phases and the (shared) midpoint.                      *)
(* ----------------------------------------------------------------- *)

Definition phi (m n : nat) (x t : R) : R := INR n * t + (INR m - INR n) * x.
Definition midf (m k : nat) (x t : R) : R := / 2 * (phi m k x t + phi m (pred k) x t).

Lemma phi_deriv : forall m n x y, derivable_pt_lim (phi m n x) y (INR n).
Proof. intros m n x y; unfold phi; apply lin_deriv. Qed.

Lemma phi_cont : forall m n x, continuity (phi m n x).
Proof. intros m n x; unfold phi; apply lin_cont. Qed.

Lemma midf_deriv : forall m k x y,
  derivable_pt_lim (midf m k x) y (/ 2 * (INR k + INR (pred k))).
Proof.
  intros m k x y; unfold midf.
  apply (derivable_pt_lim_scal (fun t => phi m k x t + phi m (pred k) x t) (/ 2) y
           (INR k + INR (pred k))).
  apply (derivable_pt_lim_plus (phi m k x) (phi m (pred k) x) y (INR k) (INR (pred k)));
    apply phi_deriv.
Qed.

Lemma midf_cont : forall m k x, continuity (midf m k x).
Proof.
  intros m k x y; unfold midf.
  apply (continuity_pt_scal (fun t => phi m k x t + phi m (pred k) x t) (/ 2) y).
  apply continuity_pt_plus; apply phi_cont.
Qed.

(* the shared per-term angle bridge: mid ∓ (x−y)/2 = φ(k) resp. φ(k−1) *)
Lemma midf_bridge : forall m k x y,
  midf m (S k) x y - (x - y) / 2 = phi m (S k) x y
  /\ midf m (S k) x y + (x - y) / 2 = phi m k x y.
Proof.
  intros m k x y; split;
    (unfold midf; replace (pred (S k)) with k by reflexivity; unfold phi; rewrite !S_INR; field).
Qed.

(* ================================================================= *)
(*  1.  cos mode.                                                     *)
(* ================================================================= *)

Definition cterm  (m k : nat) (x t : R) : R := 2 * sin (midf m k x t).
Definition cterm' (m k : nat) (x t : R) : R :=
  2 * (cos (midf m k x t) * (/ 2 * (INR k + INR (pred k)))).
Definition Gcos  (m : nat) (x t : R) : R := Rsum (fun k => cterm  m k x t) m.
Definition Gcos' (m : nat) (x t : R) : R := Rsum (fun k => cterm' m k x t) m.

Lemma cterm_deriv : forall m k x y, derivable_pt_lim (cterm m k x) y (cterm' m k x y).
Proof.
  intros m k x y; unfold cterm, cterm'.
  apply (derivable_pt_lim_scal (fun t => sin (midf m k x t)) 2 y
           (cos (midf m k x y) * (/ 2 * (INR k + INR (pred k))))).
  apply (derivable_pt_lim_comp (midf m k x) sin y (/ 2 * (INR k + INR (pred k)))
           (cos (midf m k x y))); [ apply midf_deriv | apply derivable_pt_lim_sin ].
Qed.

Lemma cterm'_cont : forall m k x, continuity (cterm' m k x).
Proof.
  intros m k x y; unfold cterm'.
  apply (continuity_pt_scal (fun t => cos (midf m k x t) * (/ 2 * (INR k + INR (pred k)))) 2 y).
  apply (continuity_pt_mult (fun t => cos (midf m k x t))
           (fun _ => / 2 * (INR k + INR (pred k))) y).
  - apply (continuity_pt_comp (midf m k x) cos y); [ apply midf_cont | apply continuity_cos ].
  - apply continuity_pt_const; intros a b; reflexivity.
Qed.

Lemma Gcos_derivable : forall m x y, derivable_pt_lim (Gcos m x) y (Gcos' m x y).
Proof.
  intros m x y; unfold Gcos, Gcos'.
  apply (Rsum_derivable (fun k => cterm m k x) (fun k => cterm' m k x) m y).
  intro k; apply cterm_deriv.
Qed.

Lemma Gcos'_cont : forall m x, continuity (Gcos' m x).
Proof.
  intros m x; apply (Rsum_cont (fun k => cterm' m k x) m); intro k; apply cterm'_cont.
Qed.

Definition gcosC (m : nat) (x : R) : C1_fun :=
  mkC1 (c1 := Gcos m x)
       (diff0 := fun t => exist _ (Gcos' m x t) (Gcos_derivable m x t))
       (Gcos'_cont m x).

Lemma gcosC_val : forall m x y, gcosC m x y = Gcos m x y.
Proof. reflexivity. Qed.

Lemma cterm_identity : forall m k x y,
  cterm m (S k) x y * sin ((x - y) / 2) = cos (phi m (S k) x y) - cos (phi m k x y).
Proof.
  intros m k x y; destruct (midf_bridge m k x y) as [E1 E2].
  unfold cterm.
  rewrite (two_sin_sin (midf m (S k) x y) ((x - y) / 2)), E1, E2; reflexivity.
Qed.

Lemma Hg_cos_mode : forall m x y,
  gcosC m x y * sin ((x - y) / 2) = cos (INR m * y) - cos (INR m * x).
Proof.
  intros m x y; rewrite gcosC_val; unfold Gcos.
  rewrite (Rsum_mult_r (fun k => cterm m k x y) (sin ((x - y) / 2)) m).
  rewrite (Rsum_ext_from1 (fun k => cterm m k x y * sin ((x - y) / 2))
             (fun k => cos (phi m k x y) - cos (phi m (pred k) x y)) m
             (fun k => cterm_identity m k x y)).
  rewrite (Rsum_telescope (fun k => cos (phi m k x y)) m).
  unfold phi.
  replace (INR m * y + (INR m - INR m) * x) with (INR m * y) by ring.
  replace (INR O * y + (INR m - INR O) * x) with (INR m * x)
    by (rewrite INR_0; ring).
  reflexivity.
Qed.

Theorem fourier_cos_mode : forall m x,
  Un_cv (fun N => SN (fun y => cos (INR m * y)) (cos_lam_cont (INR m)) N x) (cos (INR m * x)).
Proof.
  intros m x.
  exact (fourier_pointwise (fun y => cos (INR m * y)) (cos_lam_cont (INR m)) x
           (gcosC m x) (Hg_cos_mode m x)).
Qed.

(* ================================================================= *)
(*  2.  sin mode.                                                     *)
(* ================================================================= *)

Definition sterm  (m k : nat) (x t : R) : R := -2 * cos (midf m k x t).
Definition sterm' (m k : nat) (x t : R) : R :=
  -2 * ((- sin (midf m k x t)) * (/ 2 * (INR k + INR (pred k)))).
Definition Gsin  (m : nat) (x t : R) : R := Rsum (fun k => sterm  m k x t) m.
Definition Gsin' (m : nat) (x t : R) : R := Rsum (fun k => sterm' m k x t) m.

Lemma sterm_deriv : forall m k x y, derivable_pt_lim (sterm m k x) y (sterm' m k x y).
Proof.
  intros m k x y; unfold sterm, sterm'.
  apply (derivable_pt_lim_scal (fun t => cos (midf m k x t)) (-2) y
           ((- sin (midf m k x y)) * (/ 2 * (INR k + INR (pred k))))).
  apply (derivable_pt_lim_comp (midf m k x) cos y (/ 2 * (INR k + INR (pred k)))
           (- sin (midf m k x y))); [ apply midf_deriv | apply derivable_pt_lim_cos ].
Qed.

Lemma sterm'_cont : forall m k x, continuity (sterm' m k x).
Proof.
  intros m k x y; unfold sterm'.
  apply (continuity_pt_scal (fun t => (- sin (midf m k x t)) * (/ 2 * (INR k + INR (pred k)))) (-2) y).
  apply (continuity_pt_mult (fun t => - sin (midf m k x t))
           (fun _ => / 2 * (INR k + INR (pred k))) y).
  - apply continuity_pt_opp.
    apply (continuity_pt_comp (midf m k x) sin y); [ apply midf_cont | apply continuity_sin ].
  - apply continuity_pt_const; intros a b; reflexivity.
Qed.

Lemma Gsin_derivable : forall m x y, derivable_pt_lim (Gsin m x) y (Gsin' m x y).
Proof.
  intros m x y; unfold Gsin, Gsin'.
  apply (Rsum_derivable (fun k => sterm m k x) (fun k => sterm' m k x) m y).
  intro k; apply sterm_deriv.
Qed.

Lemma Gsin'_cont : forall m x, continuity (Gsin' m x).
Proof.
  intros m x; apply (Rsum_cont (fun k => sterm' m k x) m); intro k; apply sterm'_cont.
Qed.

Definition gsinC (m : nat) (x : R) : C1_fun :=
  mkC1 (c1 := Gsin m x)
       (diff0 := fun t => exist _ (Gsin' m x t) (Gsin_derivable m x t))
       (Gsin'_cont m x).

Lemma gsinC_val : forall m x y, gsinC m x y = Gsin m x y.
Proof. reflexivity. Qed.

Lemma sterm_identity : forall m k x y,
  sterm m (S k) x y * sin ((x - y) / 2) = sin (phi m (S k) x y) - sin (phi m k x y).
Proof.
  intros m k x y; destruct (midf_bridge m k x y) as [E1 E2].
  unfold sterm.
  replace (-2 * cos (midf m (S k) x y) * sin ((x - y) / 2))
    with (- (2 * cos (midf m (S k) x y) * sin ((x - y) / 2))) by ring.
  rewrite (two_cos_sin (midf m (S k) x y) ((x - y) / 2)), E1, E2; ring.
Qed.

Lemma Hg_sin_mode : forall m x y,
  gsinC m x y * sin ((x - y) / 2) = sin (INR m * y) - sin (INR m * x).
Proof.
  intros m x y; rewrite gsinC_val; unfold Gsin.
  rewrite (Rsum_mult_r (fun k => sterm m k x y) (sin ((x - y) / 2)) m).
  rewrite (Rsum_ext_from1 (fun k => sterm m k x y * sin ((x - y) / 2))
             (fun k => sin (phi m k x y) - sin (phi m (pred k) x y)) m
             (fun k => sterm_identity m k x y)).
  rewrite (Rsum_telescope (fun k => sin (phi m k x y)) m).
  unfold phi.
  replace (INR m * y + (INR m - INR m) * x) with (INR m * y) by ring.
  replace (INR O * y + (INR m - INR O) * x) with (INR m * x)
    by (rewrite INR_0; ring).
  reflexivity.
Qed.

Theorem fourier_sin_mode : forall m x,
  Un_cv (fun N => SN (fun y => sin (INR m * y)) (sin_lam_cont (INR m)) N x) (sin (INR m * x)).
Proof.
  intros m x.
  exact (fourier_pointwise (fun y => sin (INR m * y)) (sin_lam_cont (INR m)) x
           (gsinC m x) (Hg_sin_mode m x)).
Qed.

Print Assumptions fourier_cos_mode.
Print Assumptions fourier_sin_mode.

(* ================================================================= *)
(*  END FourierMode.v                                                *)
(* ================================================================= *)
