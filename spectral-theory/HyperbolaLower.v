(* ================================================================= *)
(*  HyperbolaLower.v  --  the divergence side of L(1,chi) <> 0.       *)
(*                                                                    *)
(*      sum_{n <= N*N} f(n)/sqrt n  >=  ln (N+1)                      *)
(*                                                                    *)
(*  where f = 1 * chi.  This is where CRealCharPos earns its keep:     *)
(*  f >= 0 lets every term be dropped except the perfect squares, and  *)
(*  f(m*m) >= 1 makes what is left dominate the harmonic sum, which    *)
(*  HarmonicSum.Harm_lower already bounds below by ln (N+1).           *)
(*                                                                    *)
(*  Note sqrt (INR (m*m)) = INR m EXACTLY -- no error term anywhere on *)
(*  this side.  That is the second dividend of taking x = N*N: the     *)
(*  squares that carry the divergence are precisely the integers 1..N. *)
(*                                                                    *)
(*  Paired with the (still to come) upper bound O(1) under the         *)
(*  assumption L(1,chi) = 0, this closes the argument.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith ZArith Znumtheory List.
Require Import CRealChar CRealCharPos HarmonicSum HyperbolaSplit.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- generic monotonicity facts about RS.                     *)
(* ----------------------------------------------------------------- *)

Lemma RS_le : forall F G X,
  (forall n, (1 <= n <= X)%nat -> F n <= G n) -> RS F X <= RS G X.
Proof.
  intros F G X. induction X as [| X IH]; intro H; [ cbn; lra | ].
  cbn [RS]. assert (RS F X <= RS G X) by (apply IH; intros n Hn; apply H; lia).
  pose proof (H (S X) ltac:(lia)). lra.
Qed.

Lemma RS_le_ext : forall F X Y, (X <= Y)%nat ->
  (forall n, (X < n <= Y)%nat -> 0 <= F n) -> RS F X <= RS F Y.
Proof.
  intros F X Y HXY H. induction Y as [| Y IH].
  - replace X with 0%nat by lia. apply Rle_refl.
  - destruct (Nat.eq_dec X (S Y)) as [E | E]; [ rewrite E; apply Rle_refl | ].
    cbn [RS].
    assert (RS F X <= RS F Y) by (apply IH; [ lia | intros n Hn; apply H; lia ]).
    pose proof (H (S Y) ltac:(lia)). lra.
Qed.

Lemma RS_step_ge : forall F X Y, (X < Y)%nat ->
  (forall n, (X < n <= Y)%nat -> 0 <= F n) -> RS F X + F Y <= RS F Y.
Proof.
  intros F X Y HXY H. destruct Y as [| Y]; [ lia | ].
  cbn [RS].
  assert (RS F X <= RS F Y) by (apply RS_le_ext; [ lia | intros n Hn; apply H; lia ]).
  lra.
Qed.

(* only the perfect squares are kept *)
Lemma RS_squares : forall F N,
  (forall n, (1 <= n <= N * N)%nat -> 0 <= F n) ->
  RS (fun m => F (m * m)%nat) N <= RS F (N * N).
Proof.
  intros F N. induction N as [| N IH]; intro H; [ cbn; lra | ].
  cbn [RS].
  assert (H1 : RS (fun m => F (m * m)%nat) N <= RS F (N * N))
    by (apply IH; intros n Hn; apply H; nia).
  assert (H2 : RS F (N * N) + F (S N * S N)%nat <= RS F (S N * S N)%nat).
  { apply RS_step_ge; [ nia | intros n Hn; apply H; nia ]. }
  lra.
Qed.

Lemma RS_Harm : forall N, RS (fun m => / INR m) N = Harm N.
Proof.
  induction N as [| N IH].
  - cbn [RS]. unfold Harm. cbn [seq]. symmetry. apply Rls_nil'.
  - cbn [RS]. rewrite IH, Harm_rec. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the character.                                          *)
(* ----------------------------------------------------------------- *)

Section Lower.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ZmodOrder.ord p g = (p - 1)%nat.
Hypothesis Hreal : forall n,
  ComplexField.Cconj (DirichletModP.dchar p g A n) = DirichletModP.dchar p g A n.

Definition Bt (n : nat) : R := IZR (fchi p g A n) / sqrt (INR n).

Lemma sqrtSk_pos : forall n, (1 <= n)%nat -> 0 < sqrt (INR n).
Proof.
  intros n Hn. apply sqrt_lt_R0.
  apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); lia ].
Qed.

Lemma Bt_nonneg : forall n, (1 <= n)%nat -> 0 <= Bt n.
Proof.
  intros n Hn. unfold Bt, Rdiv. apply Rmult_le_pos.
  - replace 0 with (IZR 0) by reflexivity. apply IZR_le.
    apply (fchi_nonneg p g A Hp Hg Hord Hreal n Hn).
  - apply Rlt_le, Rinv_0_lt_compat, sqrtSk_pos; lia.
Qed.

Lemma sqrt_sq_INR : forall m, sqrt (INR (m * m)) = INR m.
Proof.
  intro m. rewrite mult_INR.
  replace (INR m * INR m) with (Rsqr (INR m)) by (unfold Rsqr; ring).
  apply sqrt_Rsqr, pos_INR.
Qed.

Lemma Bt_square_ge : forall m, (1 <= m)%nat -> / INR m <= Bt (m * m)%nat.
Proof.
  intros m Hm. unfold Bt. rewrite sqrt_sq_INR.
  assert (Hm0 : 0 < INR m) by (apply Rlt_le_trans with 1; [ lra | apply (le_INR 1); lia ]).
  assert (H1 : 1 <= IZR (fchi p g A (m * m))).
  { replace 1 with (IZR 1) by reflexivity. apply IZR_le.
    apply (fchi_sq_ge1 p g A Hp Hg Hord Hreal m Hm). }
  assert (Hinv : 0 < / INR m) by (apply Rinv_0_lt_compat; exact Hm0).
  unfold Rdiv. nra.
Qed.

Theorem B_ge_harm : forall N, Harm N <= RS Bt (N * N).
Proof.
  intro N. rewrite <- RS_Harm.
  eapply Rle_trans.
  - apply RS_le. intros m Hm. apply Bt_square_ge. lia.
  - apply RS_squares. intros n Hn. apply Bt_nonneg. lia.
Qed.

Theorem B_diverges : forall N, (1 <= N)%nat -> ln (INR (S N)) <= RS Bt (N * N).
Proof.
  intros N HN. eapply Rle_trans; [ apply Harm_lower; exact HN | apply B_ge_harm ].
Qed.

End Lower.

Print Assumptions B_diverges.

(* ================================================================= *)
(*  END HyperbolaLower.v                                              *)
(* ================================================================= *)
