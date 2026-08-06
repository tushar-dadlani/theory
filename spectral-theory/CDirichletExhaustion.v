(* ================================================================= *)
(*  CDirichletExhaustion.v  —  Milestone A / B3c: square vs hyperbola.  *)
(*                                                                    *)
(*  For two C-valued sequences A, B (the terms A_d = a_d d^{-s} of two   *)
(*  Dirichlet series), the SQUARE partial product                       *)
(*     P_N = (Sum_{d<=N} A_d)(Sum_{m<=N} B_m)                            *)
(*  equals the nested double sum Q_N = Sum_{d<=N} Sum_{m<=N} A_d B_m,    *)
(*  and the HYPERBOLIC partial sum                                       *)
(*     H_N = Sum_{d<=N} Sum_{m<=N/d} A_d B_m                             *)
(*  is Q_N with each inner range truncated at N/d.  Their difference is  *)
(*  the "corner" Sum_{d<=N} Sum_{N/d<m<=N} A_d B_m, obtained by the      *)
(*  clean seq split seq 1 N = seq 1 (N/d) ++ seq (S(N/d)) (N-N/d) --     *)
(*  NO permutation / list_prod surgery.  We bound its modulus by         *)
(*     Sum_{d<=N} |A_d| * Sum_{N/d<m<=N} |B_m|,                          *)
(*  the finite estimate whose ->0 squeeze is B3d.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ComplexField Cmodulus CListSum RealMobius MobiusOverD.
Import ListNotations.
Open Scope R_scope.

(* ---- Cls distributes over pointwise Cadd ---- *)
Lemma Cls_add : forall A (f g : A -> C) l,
  Cls l (fun x => Cadd (f x) (g x)) = Cadd (Cls l f) (Cls l g).
Proof.
  intros A f g l; induction l as [|a l IH]; [ rewrite !Cls_nil; ring | ].
  rewrite !Cls_cons, IH; ring.
Qed.

(* ---- the hyperbolic partial sum and the corner remainder ---- *)
Definition Chyp (N : nat) (A B : nat -> C) : C :=
  Cls (seq 1 N) (fun d => Cls (seq 1 (N / d)) (fun m => Cmul (A d) (B m))).

Definition Ccorner (N : nat) (A B : nat -> C) : C :=
  Cls (seq 1 N) (fun d => Cls (seq (S (N / d)) (N - N / d)) (fun m => Cmul (A d) (B m))).

(* ---- seq 1 N = seq 1 (N/d) ++ seq (S(N/d)) (N - N/d) ---- *)
Lemma seq_split_div : forall N d (g : nat -> C),
  Cls (seq 1 N) g
  = Cadd (Cls (seq 1 (N / d)) g) (Cls (seq (S (N / d)) (N - N / d)) g).
Proof.
  intros N d g.
  assert (Hle : (N / d <= N)%nat)
    by (destruct d; [ simpl; lia | apply Nat.div_le_upper_bound; nia ]).
  rewrite <- Cls_app; f_equal.
  replace (S (N / d)) with (1 + N / d)%nat by lia.
  rewrite <- List.seq_app; f_equal; lia.
Qed.

(* ---- the square (= nested full double sum) ---- *)
Lemma Csq_eq_nested : forall N (A B : nat -> C),
  Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B)
  = Cls (seq 1 N) (fun d => Cls (seq 1 N) (fun m => Cmul (A d) (B m))).
Proof.
  intros N A B.
  transitivity (Cls (seq 1 N) (fun d => Cmul (Cls (seq 1 N) B) (A d))).
  - rewrite <- (Cls_scal nat (Cls (seq 1 N) B) A (seq 1 N)); ring.
  - apply Cls_ext; intros d _; rewrite <- Cls_scal; ring.
Qed.

(* ---- square = hyperbola + corner ---- *)
Lemma Csq_split : forall N (A B : nat -> C),
  Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B)
  = Cadd (Chyp N A B) (Ccorner N A B).
Proof.
  intros N A B; rewrite Csq_eq_nested; unfold Chyp, Ccorner.
  rewrite <- Cls_add; apply Cls_ext; intros d _.
  apply (seq_split_div N d (fun m => Cmul (A d) (B m))).
Qed.

(* ---- the finite tail bound: |P_N - H_N| <= Sum_d |A_d| Sum_{N/d<m<=N} |B_m| ---- *)
Theorem Csq_hyp_bound : forall N (A B : nat -> C),
  Cmod (Cminus (Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B)) (Chyp N A B))
  <= Rls (seq 1 N) (fun d => Cmod (A d)
        * Rls (seq (S (N / d)) (N - N / d)) (fun m => Cmod (B m))).
Proof.
  intros N A B; rewrite Csq_split.
  replace (Cminus (Cadd (Chyp N A B) (Ccorner N A B)) (Chyp N A B))
    with (Ccorner N A B) by ring.
  unfold Ccorner.
  eapply Rle_trans; [ apply Cmod_Cls_le | ].
  apply Rls_le; intros d _.
  eapply Rle_trans; [ apply Cmod_Cls_le | ].
  rewrite Rls_scal.
  apply Rls_le; intros m _; rewrite Cmod_mul; apply Rle_refl.
Qed.

Print Assumptions Csq_hyp_bound.

(* ================================================================= *)
(*  END CDirichletExhaustion.v  —  P_N - H_N = the corner, bounded.     *)
(* ================================================================= *)
