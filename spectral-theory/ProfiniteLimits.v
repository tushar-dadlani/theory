(* ================================================================= *)
(*  ProfiniteLimits.v                                                *)
(*                                                                    *)
(*  Analytic ZERO and MINUS INFINITY from the infinity object.        *)
(*                                                                    *)
(*  The primorial tower gives a triangle of dualities:                *)
(*    - infinity : the order-top of omega+1 (exponent -> oo)           *)
(*    - zero     : its ring limit  p^k -> 0  (i.e. p^oo = 0)           *)
(*    - -oo       : its log-size limit  log|p^k|_p = -k log p -> -oo    *)
(*                                                                    *)
(*  Core (axiom-free): p^k -> 0 in the p-adic inverse-limit tower      *)
(*  (agrees with Zzero above every level), = the order-top's ring       *)
(*  image (Phi_infty), and the order-bottom emb 0.  Reals layer (4 std  *)
(*  axioms): the radius |p^k|_p -> 0 as a Un_cv, and the log-size        *)
(*  -> -oo encoded as cv_infty of the negated (no Rbar in the repo).    *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia Reals Lra.
Require Import PadicIntegers InvLimit ChainTower ProfiniteBridge.

(* ================================================================= *)
(*  1.  Core (axiom-free): zero as the analytic limit of p^k          *)
(* ================================================================= *)

(* embed a natural into Z_p (mirror of ProfiniteInteger.embW, mod p^n) *)
Definition embZp (p z : nat) : Zp p :=
  exist (redcoh p) (fun n => z mod (p ^ n))
        (fun n => eq_sym (PadicIntegers.nested_mod p z n)).

Lemma projZ_embZp : forall p z n, projZ p n (embZp p z) = z mod (p ^ n).
Proof. reflexivity. Qed.

(* p^k -> 0 in the tower: at every level n, p^k agrees with 0 for k >= n *)
Lemma padic_pow_cv_zero : forall p n, (2 <= p)%nat ->
  exists K, forall k, (K <= k)%nat -> projZ p n (embZp p (p ^ k)) = 0.
Proof.
  intros p n Hp. exists n. intros k Hk. rewrite projZ_embZp.
  replace k with (n + (k - n))%nat by lia.
  rewrite Nat.pow_add_r, Nat.mul_comm, Nat.Div0.mod_mul. reflexivity.
Qed.

(* the ring-zero as a limit point: p^k agrees with Zzero above level n *)
Lemma padic_pow_to_Zzero : forall p n k, (2 <= p)%nat -> (n <= k)%nat ->
  projZ p n (embZp p (p ^ k)) = projZ p n (Zzero p).
Proof.
  intros p n k Hp Hk. destruct (padic_pow_cv_zero p n Hp) as [K HK].
  rewrite projZ_embZp.
  replace k with (n + (k - n))%nat by lia.
  rewrite Nat.pow_add_r, Nat.mul_comm, Nat.Div0.mod_mul. reflexivity.
Qed.

(* the order-top's ring image is 0 (p^oo = 0), from Phi_infty *)
Lemma padic_top_is_zero : forall p (Hp : (2 <= p)%nat) n,
  projZ p n (Phi p Hp infty) = 0.
Proof. intros p Hp n. rewrite Phi_infty. reflexivity. Qed.

(* the order-BOTTOM (exponent 0 everywhere), dual to infty *)
Definition Zbot : InvLim := emb 0.

Lemma bot_least : forall X, leL Zbot X.
Proof.
  intros X n. unfold Zbot, leC. rewrite emb_proj.
  unfold embseq, val; cbn [proj1_sig]. rewrite Nat.min_0_l. apply Nat.le_0_l.
Qed.

(* ================================================================= *)
(*  2.  Reals layer (4 std axioms): radius -> 0 and log-size -> -oo    *)
(* ================================================================= *)

Open Scope R_scope.

(* the p-adic radius |p^k|_p = p^{-k} -> 0 *)
Lemma padic_radius_cv0 : forall p, (2 <= p)%nat ->
  Un_cv (fun k => / INR (p ^ k)) 0.
Proof.
  intros p Hp.
  assert (Hp1 : 1 < INR p) by (apply lt_1_INR; lia).
  assert (Hpk : forall k, / INR (p ^ k) = (/ INR p) ^ k).
  { intro k. rewrite pow_INR, pow_inv; reflexivity. }
  intros eps Heps.
  destruct (pow_lt_1_zero (/ INR p)
              ltac:(rewrite Rabs_right;
                    [ apply Rmult_lt_reg_l with (INR p); [ lra | rewrite Rinv_r; lra ]
                    | left; apply Rinv_0_lt_compat; lra ])
              eps Heps) as [N HN].
  exists N. intros k Hk. rewrite Hpk. unfold R_dist. rewrite Rminus_0_r.
  apply HN; exact Hk.
Qed.

(* the log-size  log|p^k|_p = -k log p -> -oo, i.e. the negated -> +oo *)
Lemma padic_logsize_diverges : forall p, (2 <= p)%nat ->
  cv_infty (fun k => INR k * ln (INR p)).
Proof.
  intros p Hp.
  assert (Hp1 : 1 < INR p) by (apply lt_1_INR; lia).
  assert (Hln : 0 < ln (INR p)) by (rewrite <- ln_1; apply ln_increasing; lra).
  intros M. destruct (INR_unbounded (M / ln (INR p))) as [N HN].
  exists N. intros k Hk.
  apply (Rmult_lt_reg_r (/ ln (INR p))); [ apply Rinv_0_lt_compat; exact Hln | ].
  replace (INR k * ln (INR p) * / ln (INR p)) with (INR k) by (field; lra).
  apply Rlt_le_trans with (INR N); [ unfold Rdiv in HN; exact HN | apply le_INR; exact Hk ].
Qed.

(* ================================================================= *)
(*  MASTER THEOREM: the infinity / zero / -infinity triangle          *)
(* ================================================================= *)
Theorem infinity_zero_neginfty :
  (* infinity is the order-top of omega+1 *)
  (forall X, leL X infty)
  (* ... and emb 0 is the order-bottom *)
  /\ (forall X, leL Zbot X)
  (* ZERO: the order-top's ring image is 0 (p^oo = 0) *)
  /\ (forall p (Hp : (2 <= p)%nat) n, projZ p n (Phi p Hp infty) = 0%nat)
  (* ZERO analytically: p^k -> 0 in the p-adic inverse-limit tower *)
  /\ (forall p n, (2 <= p)%nat ->
        exists K, forall k, (K <= k)%nat -> projZ p n (embZp p (p ^ k)) = 0%nat)
  (* ZERO analytically (Reals): the radius |p^k|_p -> 0 *)
  /\ (forall p, (2 <= p)%nat -> Un_cv (fun k => / INR (p ^ k)) 0)
  (* MINUS INFINITY: the log-size log|p^k|_p = -k log p -> -oo *)
  /\ (forall p, (2 <= p)%nat -> cv_infty (fun k => INR k * ln (INR p))).
Proof.
  split; [ exact infty_top | ].
  split; [ exact bot_least | ].
  split; [ exact padic_top_is_zero | ].
  split; [ exact padic_pow_cv_zero | ].
  split; [ exact padic_radius_cv0 | exact padic_logsize_diverges ].
Qed.

Print Assumptions infinity_zero_neginfty.
Print Assumptions padic_pow_cv_zero.

(* ================================================================= *)
(*  END ProfiniteLimits.v                                            *)
(* ================================================================= *)
