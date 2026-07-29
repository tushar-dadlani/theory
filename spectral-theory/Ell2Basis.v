(* ================================================================= *)
(*  Ell2Basis.v  —  the standard orthonormal basis of ℓ², and the     *)
(*  eigenvectors of the diagonal operator.                           *)
(*                                                                    *)
(*  e i := the indicator sequence  n ↦ [n = i]  (1 at i, else 0).     *)
(*  We prove:                                                        *)
(*    • e i ∈ ℓ²                                    (Ell2_e);         *)
(*    • ORTHONORMALITY:  ⟨e i, e i⟩ = 1  (ip_e_diag, norm e_norm),     *)
(*                       ⟨e i, e j⟩ = 0  for i ≠ j (ip_e_off);        *)
(*    • EIGENVECTORS:  the diagonal operator D_a satisfies            *)
(*                       D_a (e i) = a(i)·(e i)     (Dmul_eigen),      *)
(*      so each a(i) is an eigenvalue — {a(i)} lies in the spectrum.  *)
(*                                                                    *)
(*  Axiom footprint: inherited from Ell2 — the standard classical-    *)
(*  Reals + functional-extensionality axioms only.                   *)
(* ================================================================= *)

Require Import Ell2 Ell2Operator.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* the standard basis vector (indicator at i) *)
Definition e (i : nat) : nat -> R := fun n => if Nat.eqb n i then 1 else 0.

Lemma e_app : forall i n, e i n = (if Nat.eqb n i then 1 else 0)%R.
Proof. reflexivity. Qed.

Lemma e_diag : forall i, e i i = 1.
Proof. intro i; unfold e; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma e_off : forall i n, n <> i -> e i n = 0.
Proof. intros i n H; unfold e; apply Nat.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma e_bound01 : forall i n, e i n = 0 \/ e i n = 1.
Proof. intros i n; unfold e; destruct (Nat.eqb n i); auto. Qed.

(* decide the boolean tests appearing in indicator partial sums *)
Ltac decideb :=
  repeat match goal with
  | [ H : Nat.leb _ _ = true  |- _ ] => apply Nat.leb_le  in H
  | [ H : Nat.leb _ _ = false |- _ ] => apply Nat.leb_gt  in H
  | [ H : Nat.eqb _ _ = true  |- _ ] => apply Nat.eqb_eq  in H
  | [ H : Nat.eqb _ _ = false |- _ ] => apply Nat.eqb_neq in H
  end.

(* the indicator partial sum: Σ_{n≤N} [n=i] = [i ≤ N] *)
Lemma sum_e_closed : forall i N,
  sum_f_R0 (e i) N = (if Nat.leb i N then 1 else 0)%R.
Proof.
  intros i N; induction N.
  - cbn [sum_f_R0]; rewrite e_app.
    destruct (Nat.eqb 0 i) eqn:E1; destruct (Nat.leb i 0) eqn:E2; cbn;
      decideb; solve [ lra | exfalso; lia ].
  - rewrite sum_f_R0_S, IHN, (e_app i (S N)).
    destruct (Nat.leb i N) eqn:E1; destruct (Nat.leb i (S N)) eqn:E2;
      destruct (Nat.eqb (S N) i) eqn:E3; cbn;
      decideb; solve [ lra | exfalso; lia ].
Qed.

(* e i is square-summable: its partial sums of squares are bounded by 1 *)
Lemma Ell2_e : forall i, Ell2 (e i).
Proof.
  intro i; apply (Summable_of_bounded (fun n => (e i n) ^ 2) 1).
  - intro n; apply pow2_ge_0.
  - intro N.
    rewrite (sum_eq (fun n => (e i n) ^ 2) (e i) N)
      by (intros k _; destruct (e_bound01 i k) as [Hk | Hk]; rewrite Hk; ring).
    rewrite sum_e_closed; destruct (Nat.leb i N); lra.
Qed.

(* the eventually-constant indicator partial sum converges to 1 *)
Lemma Un_cv_step1 : forall i, Un_cv (fun N => if Nat.leb i N then 1 else 0) 1.
Proof.
  intros i eps Heps; exists i; intros N HN.
  assert (Hb : Nat.leb i N = true) by (apply Nat.leb_le; exact HN).
  rewrite Hb; unfold R_dist; rewrite Rminus_diag_eq by reflexivity.
  rewrite Rabs_R0; exact Heps.
Qed.

(* NORMALISATION: ⟨e i, e i⟩ = 1 *)
Lemma ip_e_diag : forall i (H : Ell2 (e i)), ip (e i) (e i) H H = 1.
Proof.
  intros i H.
  apply (UL_sequence (fun N => sum_f_R0 (fun n => e i n * e i n) N)
                     (ip (e i) (e i) H H) 1).
  - apply ip_spec.
  - apply (Un_cv_eq (fun N => if Nat.leb i N then 1 else 0)); [ | apply Un_cv_step1 ].
    intro N; symmetry; transitivity (sum_f_R0 (e i) N).
    + apply sum_eq; intros k _; destruct (e_bound01 i k) as [Hk | Hk]; rewrite Hk; ring.
    + apply sum_e_closed.
Qed.

(* the basis vectors are unit vectors *)
Lemma e_norm : forall i (H : Ell2 (e i)), norm (e i) H = 1.
Proof. intros i H; unfold norm; rewrite ip_e_diag; apply sqrt_1. Qed.

(* ORTHOGONALITY: ⟨e i, e j⟩ = 0 for i ≠ j *)
Lemma ip_e_off : forall i j (Hi : Ell2 (e i)) (Hj : Ell2 (e j)),
  i <> j -> ip (e i) (e j) Hi Hj = 0.
Proof.
  intros i j Hi Hj Hij.
  apply (UL_sequence (fun N => sum_f_R0 (fun n => e i n * e j n) N)
                     (ip (e i) (e j) Hi Hj) 0).
  - apply ip_spec.
  - apply (Un_cv_eq (fun N => 0)); [ | apply Un_cv_const ].
    intro N; symmetry; transitivity (sum_f_R0 (fun _ : nat => 0) N).
    + apply sum_eq; intros k _; destruct (Nat.eq_dec k i) as [-> | Hki].
      * rewrite (e_off j i Hij); ring.
      * rewrite (e_off i k Hki); ring.
    + rewrite sum_cte; ring.
Qed.

(* EIGENVECTORS: D_a (e i) = a(i)·(e i), pointwise *)
Lemma Dmul_eigen : forall (a : nat -> R) i n, Dmul a (e i) n = (a i * e i n)%R.
Proof.
  intros a i n; unfold Dmul; destruct (Nat.eq_dec n i) as [-> | Hni].
  - reflexivity.
  - rewrite (e_off i n Hni); ring.
Qed.

Print Assumptions ip_e_diag.
Print Assumptions ip_e_off.
Print Assumptions Dmul_eigen.

(* ================================================================= *)
(*  END Ell2Basis.v                                                  *)
(*  {e i} is an orthonormal system in ℓ² (⟨e i,e j⟩ = δ_ij), and each *)
(*  e i is an eigenvector of the diagonal operator D_a with           *)
(*  eigenvalue a(i) — the point spectrum {a(i) : i ∈ ℕ}.  (Totality   *)
(*  of the basis / Parseval is the natural next increment.)          *)
(* ================================================================= *)
