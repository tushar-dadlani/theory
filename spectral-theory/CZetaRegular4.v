(* ================================================================= *)
(*  CZetaRegular4.v   (Phase B2, part 3: series remainder toolkit)     *)
(*                                                                    *)
(*  For a complex series dominated by a summable real series, the      *)
(*  complex remainder after M terms is bounded by the real remainder:  *)
(*     Cmod (S - Cpsum a M) <= Tb - sum_f_R0 b M.                       *)
(*  This is the uniform tail control for the s->1 limit of G.          *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries.
Open Scope R_scope.

(* shifting the index of a convergent sequence *)
Lemma Un_cv_shiftM : forall (u : nat -> R) l M,
  Un_cv u l -> Un_cv (fun J => u (S (M + J))) l.
Proof.
  intros u l M H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros J HJ. apply HN. lia.
Qed.

Lemma CUn_cv_shiftM : forall (u : nat -> C) l M,
  CUn_cv u l -> CUn_cv (fun J => u (S (M + J))) l.
Proof.
  intros u l M H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros J HJ. apply HN. lia.
Qed.

(* the tail partial sums telescope against the full partial sums *)
Lemma Cpsum_tail_eq : forall a M J,
  Cpsum (fun j => a (S (M + j))) J = Cminus (Cpsum a (S (M + J))) (Cpsum a M).
Proof.
  intros a M J. induction J as [| J IH].
  - simpl. rewrite Nat.add_0_r. simpl. ring.
  - simpl Cpsum. rewrite IH.
    replace (M + S J)%nat with (S (M + J))%nat by lia.
    simpl Cpsum. ring.
Qed.

Lemma sum_f_R0_tail_eq : forall b M J,
  sum_f_R0 (fun j => b (S (M + j))) J = sum_f_R0 b (S (M + J)) - sum_f_R0 b M.
Proof.
  intros b M J. induction J as [| J IH].
  - simpl. rewrite !Nat.add_0_r. ring.
  - rewrite (tech5 (fun j => b (S (M + j))) J). rewrite IH.
    replace (M + S J)%nat with (S (M + J))%nat by lia.
    rewrite (tech5 b (S (M + J))). ring.
Qed.

(* the complex remainder is bounded by the majorant's remainder *)
Lemma cseries_remainder_bound : forall (a : nat -> C) (b : nat -> R) Ssum Tb,
  Cseries_cv a Ssum ->
  (forall n, Cmod (a n) <= b n) ->
  Un_cv (sum_f_R0 b) Tb ->
  forall M, Cmod (Cminus Ssum (Cpsum a M)) <= Tb - sum_f_R0 b M.
Proof.
  intros a b Ssum Tb HS Hbd HTb M.
  (* the tail series  a (S (M + .))  converges to  Ssum - Cpsum a M *)
  assert (HtailA : Cseries_cv (fun j => a (S (M + j))) (Cminus Ssum (Cpsum a M))).
  { unfold Cseries_cv, CUn_cv. intros eps Heps.
    destruct (HS eps Heps) as [N HN]. exists N. intros J HJ.
    rewrite Cpsum_tail_eq.
    replace (Cminus (Cminus (Cpsum a (S (M + J))) (Cpsum a M)) (Cminus Ssum (Cpsum a M)))
       with (Cminus (Cpsum a (S (M + J))) Ssum) by ring.
    apply HN. lia. }
  assert (HtailB : Un_cv (sum_f_R0 (fun j => b (S (M + j)))) (Tb - sum_f_R0 b M)).
  { intros eps Heps. destruct (HTb eps Heps) as [N HN]. exists N. intros J HJ.
    rewrite sum_f_R0_tail_eq. unfold R_dist.
    replace (sum_f_R0 b (S (M + J)) - sum_f_R0 b M - (Tb - sum_f_R0 b M))
       with (sum_f_R0 b (S (M + J)) - Tb) by ring.
    apply HN. lia. }
  (* compare  |Cpsum tailA J| <= sum tailB J  in the limit *)
  apply Rle_cv_lim with (Un := fun J => Cmod (Cpsum (fun j => a (S (M + j))) J))
                        (Vn := sum_f_R0 (fun j => b (S (M + j)))).
  - intro J. eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
    apply sum_Rle. intros k _. apply Hbd.
  - intros eps Heps. destruct (HtailA eps Heps) as [N HN]. exists N. intros J HJ.
    unfold R_dist. eapply Rle_lt_trans; [ apply Cmod_diff_le | apply HN; exact HJ ].
  - exact HtailB.
Qed.
