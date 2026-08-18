(* ================================================================= *)
(*  PrimorialCircleFourier.v  —  the primorial as the angular step of   *)
(*  the circle, bridged to the Fourier / roots-of-unity machinery.      *)
(*                                                                    *)
(*  The primorial grid nprimorial(k) = prod_{i<k} q_i that tiles [0,1]   *)
(*  with N cells of width dx = 1/N (RiemannSumGeneral.riemann_grid_cv)   *)
(*  ALSO tiles the circle R/Z with ANGULAR STEP 2*PI/N.  Under           *)
(*  x |-> Cexp(2*PI*x) the grid points j/N become the N-th ROOTS OF      *)
(*  UNITY  Cpow (w N) j,  so the primorial-grid Riemann sum of a         *)
(*  Fourier mode is a DISCRETE DFT over Z/nprimorial that converges, as  *)
(*  the primorial -> oo (angular step -> 0), to the CONTINUOUS Fourier   *)
(*  coefficient on the circle.                                          *)
(*                                                                    *)
(*  Two motifs from the integral work carry over:                       *)
(*   * the ADDITIVE INDEX  1+1+...+1 = j  = j copies of the fundamental  *)
(*     step (grid_angle_index; the character homomorphism csample_add);  *)
(*   * PRIME ROTATIONS: the finer primorial root, rotated q_k times,     *)
(*     equals the coarser one (wprim_rotate); each prime subdivides the  *)
(*     angular step (angstep_subdiv); differentiation of a mode is a     *)
(*     phase advance by PI/2 (deriv_cos_mode).                           *)
(*                                                                    *)
(*  Axiom-clean (only the 4 standard classical-Reals axioms).           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import RiemannSumGeneral PrimorialRiemann
        EulerFormula RootsOfUnity CharactersModN PrimeInfinities.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Elementary phase / derivative facts                               *)
(* ----------------------------------------------------------------- *)

Lemma lin_deriv : forall c x, derivable_pt_lim (fun t => c * t) x c.
Proof.
  intros c x.
  pose proof (derivable_pt_lim_scal (fun t => t) c x 1 (derivable_pt_lim_id x)) as H.
  unfold mult_real_fct in H. rewrite Rmult_1_r in H. exact H.
Qed.

Lemma cos_shift_pi2 : forall t, cos (t + PI / 2) = - sin t.
Proof. intro t. rewrite cos_plus, cos_PI2, sin_PI2. ring. Qed.

Lemma sin_shift_pi2 : forall t, sin (t + PI / 2) = cos t.
Proof. intro t. rewrite sin_plus, cos_PI2, sin_PI2. ring. Qed.

(* ----------------------------------------------------------------- *)
(*  A. the grid angle and the circle sample point                     *)
(* ----------------------------------------------------------------- *)

(* the angle of the j-th grid point on the circle of N equal steps *)
Definition grid_angle (N j : nat) : R := 2 * PI * (INR j / INR N).

Lemma grid_angle_0 : forall N, grid_angle N 0 = 0.
Proof.
  intro N. unfold grid_angle. change (INR 0) with 0.
  unfold Rdiv. rewrite Rmult_0_l, Rmult_0_r. reflexivity.
Qed.

Lemma grid_angle_full : forall N, (0 < N)%nat -> grid_angle N N = 2 * PI.
Proof.
  intros N HN. unfold grid_angle.
  assert (INR N <> 0) by (apply not_0_INR; lia). field; assumption.
Qed.

Lemma grid_angle_step : forall N j, (0 < N)%nat ->
  grid_angle N (S j) - grid_angle N j = 2 * PI / INR N.
Proof.
  intros N j HN. unfold grid_angle. rewrite S_INR.
  assert (INR N <> 0) by (apply not_0_INR; lia). field; assumption.
Qed.

(* the additive index 1+1+...+1 = j : grid angle is j copies of the step *)
Lemma grid_angle_index : forall N j, (0 < N)%nat ->
  grid_angle N j = ones j * (2 * PI / INR N).
Proof.
  intros N j HN. unfold grid_angle. rewrite ones_eq.
  assert (INR N <> 0) by (apply not_0_INR; lia). field; assumption.
Qed.

(* the circle sample point of the j-th grid point *)
Definition csample (N j : nat) : ComplexField.C := Cexp (grid_angle N j).

Lemma Re_csample : forall N j, ComplexField.Re (csample N j) = cos (grid_angle N j).
Proof. reflexivity. Qed.

Lemma Im_csample : forall N j, ComplexField.Im (csample N j) = sin (grid_angle N j).
Proof. reflexivity. Qed.

(* THE identification: the primorial grid points ARE the N-th roots of unity *)
Lemma csample_root : forall N j, (0 < N)%nat -> csample N j = Cpow (w N) j.
Proof.
  intros N j HN. unfold csample. rewrite w_is_Cexp, Cpow_Cexp. f_equal.
  unfold grid_angle. assert (INR N <> 0) by (apply not_0_INR; lia). field; assumption.
Qed.

(* one full 2*PI turn (index j = N) lands back at 1 *)
Lemma csample_fullturn : forall N, (0 < N)%nat -> csample N N = ComplexField.C1.
Proof. intros N HN. rewrite csample_root by assumption. apply w_pow_N; assumption. Qed.

(* the sample is the additive character chi_1 evaluated at j *)
Lemma csample_chi : forall N j, (0 < N)%nat -> csample N j = chi N 1 j.
Proof.
  intros N j HN. unfold chi. rewrite Nat.mul_1_l.
  apply csample_root; assumption.
Qed.

(* additive index on the line = repeated rotation on the circle *)
Lemma csample_add : forall N i j, (0 < N)%nat ->
  csample N (i + j) = ComplexField.Cmul (csample N i) (csample N j).
Proof.
  intros N i j HN. rewrite !csample_chi by assumption. apply chi_add.
Qed.

(* ----------------------------------------------------------------- *)
(*  D. differentiation of a grid mode = phase advance by PI/2         *)
(* ----------------------------------------------------------------- *)

Lemma deriv_cos_mode : forall m x,
  derivable_pt_lim (fun t => cos (2 * PI * INR m * t)) x
    (2 * PI * INR m * cos (2 * PI * INR m * x + PI / 2)).
Proof.
  intros m x.
  pose proof (derivable_pt_lim_comp (fun t => 2 * PI * INR m * t) cos x
                (2 * PI * INR m) (- sin (2 * PI * INR m * x))
                (lin_deriv _ _) (derivable_pt_lim_cos _)) as H.
  cbv beta in H.
  replace (2 * PI * INR m * cos (2 * PI * INR m * x + PI / 2))
     with (- sin (2 * PI * INR m * x) * (2 * PI * INR m))
     by (rewrite cos_shift_pi2; ring).
  exact H.
Qed.

Lemma deriv_sin_mode : forall m x,
  derivable_pt_lim (fun t => sin (2 * PI * INR m * t)) x
    (2 * PI * INR m * sin (2 * PI * INR m * x + PI / 2)).
Proof.
  intros m x.
  pose proof (derivable_pt_lim_comp (fun t => 2 * PI * INR m * t) sin x
                (2 * PI * INR m) (cos (2 * PI * INR m * x))
                (lin_deriv _ _) (derivable_pt_lim_sin _)) as H.
  cbv beta in H.
  replace (2 * PI * INR m * sin (2 * PI * INR m * x + PI / 2))
     with (cos (2 * PI * INR m * x) * (2 * PI * INR m))
     by (rewrite sin_shift_pi2; ring).
  exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  E. the modal integrands and their continuity                      *)
(* ----------------------------------------------------------------- *)

Definition Fcos (f : R -> R) (m : nat) (x : R) : R := f x * cos (2 * PI * INR m * x).
Definition Fsin (f : R -> R) (m : nat) (x : R) : R := f x * sin (2 * PI * INR m * x).

Lemma cont_cos_mode : forall m x, continuity_pt (fun t => cos (2 * PI * INR m * t)) x.
Proof.
  intros m x. apply (continuity_pt_comp (fun t => 2 * PI * INR m * t) cos);
    [ reg | apply continuity_cos ].
Qed.

Lemma cont_sin_mode : forall m x, continuity_pt (fun t => sin (2 * PI * INR m * t)) x.
Proof.
  intros m x. apply (continuity_pt_comp (fun t => 2 * PI * INR m * t) sin);
    [ reg | apply continuity_sin ].
Qed.

Lemma cont_Fcos : forall f m, (forall x, 0 <= x <= 1 -> continuity_pt f x) ->
  forall x, 0 <= x <= 1 -> continuity_pt (Fcos f m) x.
Proof.
  intros f m Hf x Hx. unfold Fcos.
  apply continuity_pt_mult; [ apply Hf; exact Hx | apply cont_cos_mode ].
Qed.

Lemma cont_Fsin : forall f m, (forall x, 0 <= x <= 1 -> continuity_pt f x) ->
  forall x, 0 <= x <= 1 -> continuity_pt (Fsin f m) x.
Proof.
  intros f m Hf x Hx. unfold Fsin.
  apply continuity_pt_mult; [ apply Hf; exact Hx | apply cont_sin_mode ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the sample = the additive-character DFT                           *)
(* ----------------------------------------------------------------- *)

Lemma Re_chi : forall N m j, (0 < N)%nat ->
  ComplexField.Re (chi N m j) = cos (2 * PI * INR m * (INR j / INR N)).
Proof.
  intros N m j HN. unfold chi. rewrite w_is_Cexp, Cpow_Cexp.
  replace (ComplexField.Re (Cexp (INR (m * j) * (2 * PI / INR N))))
     with (cos (INR (m * j) * (2 * PI / INR N))) by reflexivity.
  f_equal. rewrite mult_INR.
  assert (INR N <> 0) by (apply not_0_INR; lia). field; assumption.
Qed.

Lemma Im_chi : forall N m j, (0 < N)%nat ->
  ComplexField.Im (chi N m j) = sin (2 * PI * INR m * (INR j / INR N)).
Proof.
  intros N m j HN. unfold chi. rewrite w_is_Cexp, Cpow_Cexp.
  replace (ComplexField.Im (Cexp (INR (m * j) * (2 * PI / INR N))))
     with (sin (INR (m * j) * (2 * PI / INR N))) by reflexivity.
  f_equal. rewrite mult_INR.
  assert (INR N <> 0) by (apply not_0_INR; lia). field; assumption.
Qed.

(* the primorial cosine sum IS the real part of the chi_m DFT over Z/N *)
Lemma sample_dft_cos : forall f N m, (0 < N)%nat ->
  Rsum (Fcos f m) N
  = / INR N * sum_f_R0 (fun j => f (INR j / INR N) * ComplexField.Re (chi N m j)) (pred N).
Proof.
  intros f N m HN. unfold Rsum. f_equal. apply sum_eq. intros i _.
  unfold Fcos. rewrite (Re_chi N m i HN). reflexivity.
Qed.

Lemma sample_dft_sin : forall f N m, (0 < N)%nat ->
  Rsum (Fsin f m) N
  = / INR N * sum_f_R0 (fun j => f (INR j / INR N) * ComplexField.Im (chi N m j)) (pred N).
Proof.
  intros f N m HN. unfold Rsum. f_equal. apply sum_eq. intros i _.
  unfold Fsin. rewrite (Im_chi N m i HN). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Section Circle : the k-indexed primorial grid                     *)
(* ----------------------------------------------------------------- *)

Section Circle.
Variable Q : nat -> nat.                    (* nat prime enumeration *)
Hypothesis HQ : forall i, (2 <= Q i)%nat.

Lemma nprim_pos : forall k, (0 < nprimorial Q k)%nat.
Proof.
  intro k. apply Nat.lt_le_trans with (2 ^ k)%nat.
  - apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia.
  - apply nprimorial_ge_pow2; exact HQ.
Qed.

(* the fundamental angular step of the primorial grid *)
Definition angstep (k : nat) : R := 2 * PI / INR (nprimorial Q k).

Lemma angstep_pos : forall k, 0 < angstep k.
Proof.
  intro k. unfold angstep. apply Rdiv_lt_0_compat.
  - pose proof PI_RGT_0; lra.
  - apply lt_0_INR; apply nprim_pos.
Qed.

(* each prime subdivides the angular step by that prime *)
Lemma angstep_subdiv : forall k, angstep (S k) = angstep k / INR (Q k).
Proof.
  intro k. unfold angstep.
  change (nprimorial Q (S k)) with (nprimorial Q k * Q k)%nat.
  rewrite mult_INR.
  assert (0 < INR (nprimorial Q k)) by (apply lt_0_INR; apply nprim_pos).
  assert (0 < INR (Q k)) by (apply lt_0_INR; pose proof (HQ k); lia).
  field; split; lra.
Qed.

(* the fundamental step collapses to 0 : the grid becomes dense on the circle *)
Lemma angstep_cv0 : Un_cv angstep 0.
Proof.
  intros eps Heps.
  destruct (nprimorial_cv_infty Q HQ (2 * PI / eps)) as [K HK].
  exists K. intros k Hk. unfold R_dist, angstep. rewrite Rminus_0_r.
  assert (Hpi : 0 < 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (Hn : 2 * PI / eps < INR (nprimorial Q k)) by (apply HK; exact Hk).
  assert (Hn0 : 0 < INR (nprimorial Q k)) by (apply lt_0_INR; apply nprim_pos).
  rewrite Rabs_right by (apply Rle_ge; apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  apply Rmult_lt_reg_r with (INR (nprimorial Q k)); [ exact Hn0 | ].
  unfold Rdiv at 1. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
  apply Rmult_lt_reg_l with (/ eps); [ apply Rinv_0_lt_compat; exact Heps | ].
  replace (/ eps * (eps * INR (nprimorial Q k))) with (INR (nprimorial Q k)) by (field; lra).
  replace (/ eps * (2 * PI)) with (2 * PI / eps) by (field; lra).
  exact Hn.
Qed.

(* PRIME ROTATION: the finer primorial root, rotated Q k times, = the coarser one *)
Lemma wprim_rotate : forall k,
  Cpow (w (nprimorial Q (S k))) (Q k) = w (nprimorial Q k).
Proof.
  intro k. rewrite w_is_Cexp, Cpow_Cexp, w_is_Cexp. f_equal.
  change (nprimorial Q (S k)) with (nprimorial Q k * Q k)%nat.
  rewrite mult_INR.
  assert (0 < INR (nprimorial Q k)) by (apply lt_0_INR; apply nprim_pos).
  assert (0 < INR (Q k)) by (apply lt_0_INR; pose proof (HQ k); lia).
  field; split; lra.
Qed.

(* the grid angle at level k is j copies of the fundamental step *)
Lemma grid_angle_prim : forall k j,
  grid_angle (nprimorial Q k) j = ones j * angstep k.
Proof. intros k j. apply grid_angle_index. apply nprim_pos. Qed.

(* ===== the payoff: primorial DFT -> continuous Fourier coefficient ===== *)
Theorem primorial_fourier_cos : forall f
    (Hf : forall x, 0 <= x <= 1 -> continuity_pt f x) (m : nat),
  Un_cv (fun k => Rsum (Fcos f m) (nprimorial Q k))
        (iv (Fcos f m) (cont_Fcos f m Hf) 0 1).
Proof. intros f Hf m. apply riemann_grid_cv. exact HQ. Qed.

Theorem primorial_fourier_sin : forall f
    (Hf : forall x, 0 <= x <= 1 -> continuity_pt f x) (m : nat),
  Un_cv (fun k => Rsum (Fsin f m) (nprimorial Q k))
        (iv (Fsin f m) (cont_Fsin f m Hf) 0 1).
Proof. intros f Hf m. apply riemann_grid_cv. exact HQ. Qed.

(* ===== the whole bridge, bundled ===== *)
Theorem primorial_circle_fourier : forall f
    (Hf : forall x, 0 <= x <= 1 -> continuity_pt f x) (m : nat),
  (* angular step collapses (grid dense on circle) *)
  Un_cv angstep 0
  (* prime rotation: finer root^prime = coarser root *)
  /\ (forall k, Cpow (w (nprimorial Q (S k))) (Q k) = w (nprimorial Q k))
  (* the grid points ARE the roots of unity = additive characters *)
  /\ (forall k j, csample (nprimorial Q k) j = chi (nprimorial Q k) 1 j)
  (* additive index on the line = repeated rotation on the circle *)
  /\ (forall k i j, csample (nprimorial Q k) (i + j)
        = ComplexField.Cmul (csample (nprimorial Q k) i) (csample (nprimorial Q k) j))
  (* the grid cosine sum = real part of the chi_m DFT over Z/nprimorial *)
  /\ (forall k, Rsum (Fcos f m) (nprimorial Q k)
        = / INR (nprimorial Q k)
          * sum_f_R0 (fun j => f (INR j / INR (nprimorial Q k))
                               * ComplexField.Re (chi (nprimorial Q k) m j))
              (pred (nprimorial Q k)))
  (* discrete DFT -> continuous Fourier coefficient in the primorial limit *)
  /\ Un_cv (fun k => Rsum (Fcos f m) (nprimorial Q k))
           (iv (Fcos f m) (cont_Fcos f m Hf) 0 1).
Proof.
  intros f Hf m.
  split; [ exact angstep_cv0 | ].
  split; [ exact wprim_rotate | ].
  split; [ intros k j; apply csample_chi; apply nprim_pos | ].
  split; [ intros k i j; apply csample_add; apply nprim_pos | ].
  split; [ intros k; apply sample_dft_cos; apply nprim_pos | ].
  apply primorial_fourier_cos.
Qed.

End Circle.

Print Assumptions primorial_circle_fourier.
Print Assumptions primorial_fourier_cos.
