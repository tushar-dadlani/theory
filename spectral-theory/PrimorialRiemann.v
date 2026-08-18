(* ================================================================= *)
(*  PrimorialRiemann.v  —  a concrete Riemann sum over the primorial     *)
(*  grid converging to an integral.                                     *)
(*                                                                    *)
(*  The nat-valued primorial nprimorial(k) = prod_{i<k} q_i gives a       *)
(*  uniform partition of [0,1] into N = nprimorial(k) cells of width      *)
(*  dx = 1/N.  The left Riemann sum                                      *)
(*    Rsum f N = (1/N) . sum_{j=0}^{N-1} f(j/N)                         *)
(*  over this grid converges, as k -> oo (N -> oo), to the integral.     *)
(*  We prove the concrete instance f(x) = x:                             *)
(*                                                                    *)
(*    Rsum id N = (N-1)/(2N),   int_0^1 x dx = 1/2,                     *)
(*    riemann_grid_id : Un_cv (fun k => Rsum id (nprimorial k))          *)
(*                            (RiemannInt id_int)   (= 1/2).            *)
(*                                                                    *)
(*  i.e. dx . sum f = the integral in the primorial (hyperfinite) limit. *)
(*  The general continuous-f version is the natural next step (uniform   *)
(*  continuity + RiemannInt partition additivity).  Axiom-clean.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ContinuousCoV.
Open Scope R_scope.

(* ---- elementary sums ---- *)
Lemma sum_scal : forall (f : nat -> R) (a : R) (m : nat),
  sum_f_R0 (fun j => a * f j) m = a * sum_f_R0 f m.
Proof. intros f a m; induction m as [| m IH]; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma gauss_sum2 : forall m, 2 * sum_f_R0 (fun j => INR j) m = INR m * INR (S m).
Proof.
  induction m as [| m IH]; [ simpl; ring | ].
  rewrite tech5, Rmult_plus_distr_l, IH, !S_INR. ring.
Qed.

Lemma gauss_sum : forall m, sum_f_R0 (fun j => INR j) m = INR m * INR (S m) / 2.
Proof. intro m. pose proof (gauss_sum2 m). lra. Qed.

(* ---- the left Riemann sum over N cells ---- *)
Definition Rsum (f : R -> R) (N : nat) : R :=
  / INR N * sum_f_R0 (fun j => f (INR j / INR N)) (pred N).

Lemma Rsum_id_val : forall N, (1 <= N)%nat ->
  Rsum (fun x => x) N = (INR N - 1) / (2 * INR N).
Proof.
  intros N HN. destruct N as [| m]; [ lia | ].
  unfold Rsum; cbn [pred].
  rewrite (sum_eq (fun j => INR j / INR (S m)) (fun j => / INR (S m) * INR j))
    by (intros; unfold Rdiv; ring).
  rewrite sum_scal, gauss_sum, !S_INR.
  assert (Hm' : INR m + 1 <> 0) by (pose proof (pos_INR m); lra).
  field; exact Hm'.
Qed.

(* ---- int_0^1 x dx = 1/2 (FTC) ---- *)
Lemma cont_id : forall x, continuity_pt (fun t => t) x.
Proof. intro x. apply derivable_continuous_pt. exists 1. apply derivable_pt_lim_id. Qed.

Definition id_int : Riemann_integrable (fun x => x) 0 1 :=
  continuity_implies_RiemannInt (Rlt_le _ _ Rlt_0_1)
    (fun (x : R) (_ : 0 <= x <= 1) => cont_id x).

Lemma dhalf_sq : forall x, derivable_pt_lim (fun t => / 2 * (t * t)) x x.
Proof.
  intro x.
  assert (H2 : derivable_pt_lim (fun t => t * t) x (2 * x))
    by (replace (2 * x) with (1 * x + x * 1) by ring;
        apply derivable_pt_lim_mult; apply derivable_pt_lim_id).
  apply (derivable_pt_lim_scal (fun t => t * t) (/ 2) x (2 * x)) in H2.
  assert (Heq : / 2 * (2 * x) = x) by field. rewrite Heq in H2. exact H2.
Qed.

Lemma int_id_val : RiemannInt id_int = / 2.
Proof.
  assert (Hanti : antiderivative (fun x => x) (fun t => / 2 * (t * t)) 0 1).
  { split; [ | lra ]. intros x _.
    exists (exist (fun l => derivable_pt_lim (fun t => / 2 * (t * t)) x l) x (dhalf_sq x)).
    reflexivity. }
  rewrite (FTC_antideriv (fun x => x) (fun t => / 2 * (t * t)) 0 1
             (Rlt_le _ _ Rlt_0_1) (fun x _ => cont_id x) id_int Hanti).
  lra.
Qed.

(* ---- the nat-valued primorial grid ---- *)
Section Grid.
Variable Q : nat -> nat.                    (* nat prime enumeration *)
Hypothesis HQ : forall i, (2 <= Q i)%nat.   (* each prime >= 2 *)

Fixpoint nprimorial (k : nat) : nat :=
  match k with 0 => 1 | S k' => nprimorial k' * Q k' end.

Lemma nprimorial_ge_pow2 : forall k, (2 ^ k <= nprimorial k)%nat.
Proof.
  induction k as [| k IH]; cbn [nprimorial Nat.pow]; [ lia | ].
  apply Nat.le_trans with (2 ^ k * 2)%nat; [ lia | ].
  apply Nat.mul_le_mono; [ exact IH | apply HQ ].
Qed.

Lemma pow2_gt_lin : forall k, (S k <= 2 ^ k)%nat.
Proof.
  induction k as [| k IH]; cbn [Nat.pow]; [ lia | ]. lia.
Qed.

Lemma nprimorial_cv_infty : cv_infty (fun k => INR (nprimorial k)).
Proof.
  intro M. destruct (INR_unbounded M) as [N HN]. exists N. intros k Hk.
  assert (Hge : (S k <= nprimorial k)%nat)
    by (apply Nat.le_trans with (2 ^ k)%nat; [ apply pow2_gt_lin | apply nprimorial_ge_pow2 ]).
  assert (INR N <= INR k) by (apply le_INR; exact Hk).
  assert (INR (S k) <= INR (nprimorial k)) by (apply le_INR; exact Hge).
  rewrite S_INR in *. lra.
Qed.

(* THE concrete Riemann sum over the primorial grid -> the integral *)
Theorem riemann_grid_id :
  Un_cv (fun k => Rsum (fun x => x) (nprimorial k)) (RiemannInt id_int).
Proof.
  rewrite int_id_val.
  (* Rsum id (nprimorial k) = (a k - 1)/(2 a k), a k = INR(nprimorial k) -> inf *)
  intros eps Heps.
  destruct (nprimorial_cv_infty (/ (2 * eps))) as [N HN].
  exists N. intros k Hk.
  assert (Hpos : (1 <= nprimorial k)%nat)
    by (apply Nat.le_trans with (2 ^ k)%nat; [ apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia
                                             | apply nprimorial_ge_pow2 ]).
  rewrite Rsum_id_val by exact Hpos.
  set (a := INR (nprimorial k)) in *.
  assert (Ha : / (2 * eps) < a) by (apply HN; exact Hk).
  assert (Ha0 : 0 < a) by (apply Rlt_trans with (/ (2 * eps));
                           [ apply Rinv_0_lt_compat; lra | exact Ha ]).
  unfold R_dist.
  replace ((a - 1) / (2 * a) - / 2) with (- (/ (2 * a))) by (field; lra).
  rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat; lra).
  (* /(2a) < eps  since a > /(2 eps) *)
  apply Rmult_lt_reg_l with (2 * a); [ lra | ].
  rewrite Rinv_r by lra.
  apply Rmult_lt_reg_r with (/ (2 * eps)); [ apply Rinv_0_lt_compat; lra | ].
  rewrite Rmult_1_l.
  replace (2 * a * eps * / (2 * eps)) with a by (field; lra).
  exact Ha.
Qed.

End Grid.

Print Assumptions int_id_val.
Print Assumptions riemann_grid_id.
