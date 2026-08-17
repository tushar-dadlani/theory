(* ================================================================= *)
(*  EtaZeta.v  —  the Dirichlet eta identity  eta(s) = (1 - 2^{1-s}) zeta(s), *)
(*  connected to the repo's continued zeta  (Ell2ZetaCont.zeta_cont).      *)
(*                                                                    *)
(*  The global (-2)/alternating <-> zeta connection completing the         *)
(*  FirstPrimeZeta capstone.  The alternating zeta ("eta") is the sum that  *)
(*  "oscillates by odd and even" (Stage 3's (-2)^inf); its closed form      *)
(*  pulls out exactly the first prime via the factor 2^{1-s}:              *)
(*                                                                    *)
(*     sum_{n>=1} (-1)^{n-1} n^{-s}  =  (1 - 2^{1-s}) . zeta(s).            *)
(*                                                                    *)
(*  Two forms (real, s>1):                                                *)
(*    eta_from_zeta  — abstract: if the zeta series -> Z, the alternating   *)
(*        partial sums (even cutoffs) -> (1 - 2^{1-s}) Z.                   *)
(*    eta_zeta_cont — CONNECTED to the repo's zeta: for s>1 the alternating *)
(*        partial sums converge to  (1 - 2^{1-s}) . zeta_cont s.  The       *)
(*        bridge Zp N = dzeta s (S N) = diag_trace (z s) (S N) (the operator*)
(*        partition trace) uses the recurrence dzeta_S (seq_S/map_app/       *)
(*        fold_right_app) and operator_zeta_eq_cont (Tr Z_s -> zeta_cont).  *)
(*                                                                    *)
(*  Engine: eta_partial_id (induction; even terms pulled via z(2n)=z(2)z(n),*)
(*  parity powers m1_pow_even/m1_pow_odd reused from CountTwoCollapse), then *)
(*  a limit passage (subsequence + CV_minus + CV_mult).                    *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Import ListNotations.
Require Import Ell2Zeta Ell2ZetaCont CountTwoCollapse.
Open Scope R_scope.

Lemma z_1 : forall s, z s 1 = 1.
Proof.
  intro s. unfold z. simpl. replace (INR 1) with 1 by (simpl; ring).
  unfold Rpower. rewrite ln_1, Rmult_0_r, exp_0. reflexivity.
Qed.

Lemma z_mult2 : forall s n, (1 <= n)%nat -> z s (2 * n) = z s 2 * z s n.
Proof.
  intros s n Hn. unfold z.
  destruct (Nat.eqb (2 * n) 0) eqn:E1; [ apply Nat.eqb_eq in E1; lia | ].
  destruct (Nat.eqb 2 0) eqn:E2; [ discriminate | ].
  destruct (Nat.eqb n 0) eqn:E3; [ apply Nat.eqb_eq in E3; lia | ].
  rewrite (Rpower_mult_distr (INR 2) (INR n) (- s)
               (lt_0_INR 2 ltac:(lia)) (lt_0_INR n ltac:(lia))).
  rewrite <- mult_INR. reflexivity.
Qed.

(* the partial-sum eta identity, at even cutoffs (2M+2 terms) *)
Lemma eta_partial_id : forall s M,
  sum_f_R0 (fun i => (-1) ^ i * z s (S i)) (2 * M + 1)
  = sum_f_R0 (fun i => z s (S i)) (2 * M + 1)
    - 2 * z s 2 * sum_f_R0 (fun i => z s (S i)) M.
Proof.
  intros s. induction M as [| M IH].
  - simpl. rewrite (z_1 s). ring.
  - replace (2 * S M + 1)%nat with (S (S (2 * M + 1))) by lia.
    rewrite (tech5 (fun i => (-1) ^ i * z s (S i)) (S (2 * M + 1))).
    rewrite (tech5 (fun i => (-1) ^ i * z s (S i)) (2 * M + 1)).
    rewrite (tech5 (fun i => z s (S i)) (S (2 * M + 1))).
    rewrite (tech5 (fun i => z s (S i)) (2 * M + 1)).
    rewrite (tech5 (fun i => z s (S i)) M).
    (* the two new alternating signs: (-1)^(S(2M+1)) = +1, (-1)^(S(S(2M+1))) = -1 *)
    replace ((-1) ^ (S (2 * M + 1))) with 1
      by (replace (S (2 * M + 1)) with (2 * (M + 1))%nat by lia; rewrite m1_pow_even; reflexivity).
    replace ((-1) ^ (S (S (2 * M + 1)))) with (-1)
      by (replace (S (S (2 * M + 1))) with (S (2 * (M + 1)))%nat by lia; rewrite m1_pow_odd; reflexivity).
    (* z s (S(S(S(2M+1)))) = z s (2*(M+2)) = z s 2 * z s (M+2); and S(S M) = M+2 *)
    replace (S (S (S (2 * M + 1)))) with (2 * (M + 2))%nat by lia.
    rewrite (z_mult2 s (M + 2) ltac:(lia)).
    replace (S (S M)) with (M + 2)%nat by lia.
    rewrite IH. ring.
Qed.

Print Assumptions eta_partial_id.

Lemma Un_cv_const_loc : forall c, Un_cv (fun _ => c) c.
Proof.
  intros c eps Heps. exists 0%nat. intros n _. unfold R_dist.
  replace (c - c) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

Lemma Un_cv_subseq : forall u l (phi : nat -> nat),
  (forall M, (M <= phi M)%nat) -> Un_cv u l -> Un_cv (fun M => u (phi M)) l.
Proof.
  intros u l phi Hphi Hu eps Heps. destruct (Hu eps Heps) as [N HN].
  exists N. intros M HM. apply HN. apply Nat.le_trans with M; [ exact HM | apply Hphi ].
Qed.

Lemma two_z2 : forall s, 2 * z s 2 = Rpower 2 (1 - s).
Proof.
  intro s. unfold z. simpl.
  replace (INR 2) with 2 by (simpl; ring).
  replace (1 - s) with (1 + (- s)) by ring.
  rewrite Rpower_plus, Rpower_1 by lra. reflexivity.
Qed.

(* THE ETA IDENTITY (limit form): if the zeta series -> Z, the alternating
   partial sums -> (1 - 2^{1-s}) Z. *)
Theorem eta_from_zeta : forall s Z,
  Un_cv (fun N => sum_f_R0 (fun i => z s (S i)) N) Z ->
  Un_cv (fun M => sum_f_R0 (fun i => (-1) ^ i * z s (S i)) (2 * M + 1))
        ((1 - Rpower 2 (1 - s)) * Z).
Proof.
  intros s Z HZ.
  replace ((1 - Rpower 2 (1 - s)) * Z) with (Z - 2 * z s 2 * Z)
    by (rewrite two_z2; ring).
  apply (Un_cv_ext (fun M => sum_f_R0 (fun i => z s (S i)) (2 * M + 1)
                             - 2 * z s 2 * sum_f_R0 (fun i => z s (S i)) M)).
  - intro M. symmetry. apply eta_partial_id.
  - apply CV_minus.
    + apply (Un_cv_subseq _ _ (fun M => (2 * M + 1)%nat)); [ intro M; lia | exact HZ ].
    + apply (CV_mult (fun _ => 2 * z s 2) (fun N => sum_f_R0 (fun i => z s (S i)) N)
               (2 * z s 2) Z); [ apply Un_cv_const_loc | exact HZ ].
Qed.



(* ===== bridge to the repo's actual zeta_cont ===== *)
Lemma fold_add_init : forall (l : list R) a,
  fold_right Rplus a l = fold_right Rplus 0 l + a.
Proof. induction l as [| h t IH]; intro a; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma dzeta_S : forall s N, dzeta s (S N) = dzeta s N + z s (S N).
Proof.
  intros s N. unfold dzeta.
  rewrite seq_S, map_app, fold_right_app. simpl.
  replace (1 + N)%nat with (S N) by lia.
  rewrite fold_add_init. ring.
Qed.

Lemma zp_eq_dzeta : forall s N, sum_f_R0 (fun i => z s (S i)) N = dzeta s (S N).
Proof.
  intros s N. induction N as [| N IH].
  - simpl. rewrite (dzeta_S s 0). unfold dzeta; simpl; ring.
  - rewrite (tech5 (fun i => z s (S i)) N), IH, (dzeta_S s (S N)). reflexivity.
Qed.

Lemma zp_cv_zeta_cont : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  Un_cv (fun N => sum_f_R0 (fun i => z s (S i)) N) (zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 Hgt.
  assert (Hdz : Un_cv (dzeta s) (zeta_cont s Hs0 Hs1)).
  { apply (Un_cv_ext (fun N => diag_trace (z s) N)).
    - intro N. apply zeta_partition.
    - apply operator_zeta_eq_cont; exact Hgt. }
  apply (Un_cv_ext (fun N => dzeta s (S N))).
  - intro N. symmetry. apply zp_eq_dzeta.
  - apply (Un_cv_subseq (dzeta s) (zeta_cont s Hs0 Hs1) (fun N => S N));
      [ intro N; lia | exact Hdz ].
Qed.

(* THE ETA IDENTITY connected to the repo's zeta: for s>1, the alternating
   partial sums converge to (1 - 2^{1-s}) . zeta_cont s. *)
Theorem eta_zeta_cont : forall s (Hs0 : 0 < s) (Hs1 : s <> 1), 1 < s ->
  Un_cv (fun M => sum_f_R0 (fun i => (-1) ^ i * z s (S i)) (2 * M + 1))
        ((1 - Rpower 2 (1 - s)) * zeta_cont s Hs0 Hs1).
Proof.
  intros s Hs0 Hs1 Hgt. apply eta_from_zeta. apply zp_cv_zeta_cont; exact Hgt.
Qed.

Print Assumptions eta_zeta_cont.
