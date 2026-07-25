(* ================================================================= *)
(*  IntPolyDerivResp.v                                               *)
(*                                                                    *)
(*  ℤ[X] polynomial identity theorem (eval ≡ coeff), and that the    *)
(*  formal derivative respects functional equality.  (Toward the      *)
(*  prime-divisor lemma: differentiating X^n−1 = Φ_e·Φ_n·R.)         *)
(*                                                                    *)
(*  ℤ-PIT is obtained by embedding into ℚ[X] and using the ℚ identity *)
(*  theorem (QPolyTransfer.qeval_ext_Z + QPolyDeriv.qeval_ext_coeff). *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia Arith QArith Qcanon.
Import ListNotations.
Require Import IntPoly PolyDiv PolyMonic IntPolyDeriv
        QPoly QPolyDeriv QPolyEmbed QPolyTransfer CyclotomicProd.
Open Scope Z_scope.

(* ---- ℤ polynomial identity theorem, via the embedding ---- *)
Theorem eval_ext_coeff_Z : forall p q,
  (forall a : Z, eval p a = eval q a) -> forall i, coeff p i = coeff q i.
Proof.
  intros p q H i; apply Z2Qc_inj; rewrite <- !qcoeff_emb.
  apply (qeval_ext_coeff (emb p) (emb q)).
  apply qeval_ext_Z; intro a; rewrite !qeval_emb, (H a); reflexivity.
Qed.

(* ---- easy direction: coeff-equal ⟹ eval-equal ---- *)
Lemma peval_all_zero : forall p, (forall i, coeff p i = 0) -> forall a, eval p a = 0.
Proof.
  induction p as [|c p' IH]; intros H a; [ reflexivity | ].
  simpl; rewrite (IH (fun i => H (S i)) a).
  assert (c = 0) by (specialize (H 0%nat); unfold coeff in H; simpl in H; exact H).
  rewrite H0; ring.
Qed.

Lemma coeff_ext_eval_Z : forall p q,
  (forall i, coeff p i = coeff q i) -> forall a, eval p a = eval q a.
Proof.
  induction p as [|c p IH]; intros [|d q] H a; simpl; try reflexivity.
  - assert (H0 : forall j, coeff q j = 0)
      by (intro j; change (coeff q j) with (coeff (d :: q) (S j)); rewrite <- (H (S j)); apply coeff_nil).
    rewrite (peval_all_zero q H0 a).
    pose proof (H 0%nat) as H1; unfold coeff in H1; simpl in H1; rewrite <- H1; ring.
  - assert (H0 : forall j, coeff p j = 0)
      by (intro j; change (coeff p j) with (coeff (c :: p) (S j)); rewrite (H (S j)); apply coeff_nil).
    rewrite (peval_all_zero p H0 a).
    pose proof (H 0%nat) as H1; unfold coeff in H1; simpl in H1; rewrite H1; ring.
  - rewrite (IH q (fun j => H (S j)) a).
    pose proof (H 0%nat) as H1; unfold coeff in H1; simpl in H1; rewrite H1; ring.
Qed.

(* ---- derivative coefficient formula ---- *)
Lemma pcoeff_pderiv_aux : forall p k i,
  coeff (pderiv_aux p k) i = Z.of_nat (k + i) * coeff p i.
Proof.
  induction p as [|c p' IH]; intros k i.
  - rewrite coeff_nil; simpl; rewrite coeff_nil; ring.
  - destruct i as [|i]; unfold coeff; simpl.
    + rewrite Nat.add_0_r; reflexivity.
    + change (nth i (pderiv_aux p' (S k)) 0%Z) with (coeff (pderiv_aux p' (S k)) i).
      rewrite (IH (S k) i); replace (S k + i)%nat with (k + S i)%nat by lia; reflexivity.
Qed.

Lemma pcoeff_pderiv : forall p i, coeff (pderiv p) i = Z.of_nat (S i) * coeff p (S i).
Proof.
  intros [|c p'] i.
  - rewrite !coeff_nil; ring.
  - unfold pderiv; rewrite pcoeff_pderiv_aux; replace (1 + i)%nat with (S i) by lia; reflexivity.
Qed.

(* ---- the derivative respects functional equality ---- *)
Theorem pderiv_resp_eval : forall p q,
  (forall a, eval p a = eval q a) -> forall a, eval (pderiv p) a = eval (pderiv q) a.
Proof.
  intros p q H; apply coeff_ext_eval_Z; intro i.
  rewrite !pcoeff_pderiv, (eval_ext_coeff_Z p q H (S i)); reflexivity.
Qed.

Print Assumptions pderiv_resp_eval.

(* ================================================================= *)
(*  END IntPolyDerivResp.v                                           *)
(*  ℤ[X] identity theorem and derivative-respects-equality.  Closed   *)
(*  under the global context (axiom-free).                           *)
(* ================================================================= *)
