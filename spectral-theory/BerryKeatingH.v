(* ================================================================= *)
(*  BerryKeatingH.v                                                   *)
(*                                                                    *)
(*  THE Berry-Keating Hamiltonian H = q p + p q in the free           *)
(*  *-algebra (BerryKeatingFree), with two candidate states, turning  *)
(*  the generic BK_reality into concrete statements about H:          *)
(*                                                                    *)
(*    - H is self-adjoint (H_selfadj), with H = 1 exactly on the two  *)
(*      length-2 words q p and p q (H_qp, H_pq);                       *)
(*    - the VACUUM state  omega0 a = a([])  is Hermitian AND positive  *)
(*      (omega0 (a^dag a) = |a([])|^2 >= 0);  omega0 H = 0;            *)
(*    - the SEAM state  omegaS a = a(q p) + a(p q)  is Hermitian and   *)
(*      SEES H:  omegaS H = 2  (a nonzero REAL value);                 *)
(*    - in BOTH states the expectation of H is real                   *)
(*      (BK_H_real_vacuum, BK_H_real_seam), from selfadj_real --       *)
(*      the Berry-Keating reality condition, now for the actual H.     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals + functional_extensionality.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List.
Require Import ComplexField BerryKeating BerryKeatingFree.
Import ListNotations.
Open Scope R_scope.

(* the dilation Hamiltonian H = q p + p q *)
Definition H : Elt := Fadd (Fmul q p) (Fmul p q).

Lemma H_selfadj : SelfAdj Free_DagAlg H.
Proof. exact symmetrised_selfadj_free. Qed.

Lemma H_qp : H [gq; gp] = C1.
Proof. unfold H, Fadd, Fmul, splits, q, p; simpl; apply Ceq; simpl; ring. Qed.
Lemma H_pq : H [gp; gq] = C1.
Proof. unfold H, Fadd, Fmul, splits, q, p; simpl; apply Ceq; simpl; ring. Qed.

(* ---- the vacuum (counit) state:  positive AND Hermitian ---- *)
Definition omega0 (a : Elt) : C := a [].

Lemma omega0_dag : forall a, omega0 (Odag Free_DagAlg a) = Cconj (omega0 a).
Proof. intro a; unfold omega0; cbn; reflexivity. Qed.

Lemma omega0_positive : forall a,
  0 <= Re (omega0 (Ocomp Free_DagAlg (Odag Free_DagAlg a) a))
  /\ Im (omega0 (Ocomp Free_DagAlg (Odag Free_DagAlg a) a)) = 0.
Proof.
  intro a. unfold omega0, Ocomp, Free_DagAlg, Odag, Fmul, splits; cbn.
  unfold Fdag, Cmul, Cconj; simpl. split; [ nra | ring ].
Qed.

Lemma omega0_H : omega0 H = C0.
Proof. unfold omega0, H, Fadd, Fmul, splits, q, p; simpl; apply Ceq; simpl; ring. Qed.

(* ---- the seam state:  Hermitian, and it SEES H ---- *)
Definition omegaS (a : Elt) : C := Cadd (a [gq; gp]) (a [gp; gq]).

Lemma omegaS_dag : forall a, omegaS (Odag Free_DagAlg a) = Cconj (omegaS a).
Proof.
  intro a; unfold omegaS; cbn. unfold Fdag; simpl.
  rewrite Cconj_add; apply Cadd_comm'.
Qed.

Lemma omegaS_H : omegaS H = RtoC 2.
Proof.
  unfold omegaS. rewrite H_qp, H_pq. apply Ceq; simpl; ring.
Qed.

(* ================================================================= *)
(*  BERRY-KEATING REALITY for the actual H, in both states.          *)
(* ================================================================= *)

Theorem BK_H_real_vacuum : Im (omega0 H) = 0.
Proof. apply (selfadj_real Free_DagAlg omega0 omega0_dag); exact H_selfadj. Qed.

Theorem BK_H_real_seam : Im (omegaS H) = 0.
Proof. apply (selfadj_real Free_DagAlg omegaS omegaS_dag); exact H_selfadj. Qed.

Print Assumptions BK_H_real_seam.
Print Assumptions omegaS_H.
