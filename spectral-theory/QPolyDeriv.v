(* ================================================================= *)
(*  QPolyDeriv.v                                                     *)
(*                                                                    *)
(*  THE FORMAL DERIVATIVE in ℚ[X] (brick 5c, derivative part).      *)
(*                                                                    *)
(*  qderiv p differentiates coefficient-wise (c_k · X^k ↦ k c_k       *)
(*  X^{k−1}).  Delivered: the PRODUCT RULE                           *)
(*     (p·q)′ = p′·q + p·q′   (at eval level),                       *)
(*  that qderiv respects functional equality (via coeff-PIT), and     *)
(*  (X^n−1)′ = n·X^{n−1}.  Together with the ℚ[X] gcd this gives      *)
(*  squarefreeness of X^n−1.  AXIOM-FREE.                            *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDeg QPolyGcd QPolyCoeffPIT.
Open Scope Qc_scope.

(* --- rational arithmetic on the naturals qnat --- *)
Lemma Q2Qc_plus : forall a b, (Q2Qc a + Q2Qc b) = Q2Qc (a + b).
Proof.
  intros a b; unfold Qcplus; apply Q2Qc_eq_iff.
  change (this (Q2Qc a)) with (Qred a); change (this (Q2Qc b)) with (Qred b).
  rewrite !Qred_correct; reflexivity.
Qed.

Lemma qnat_1 : qnat 1 = 1.
Proof. reflexivity. Qed.

Lemma qnat_S : forall k, qnat (S k) = qnat k + 1.
Proof.
  intro k; unfold qnat; change 1 with (Q2Qc 1); rewrite Q2Qc_plus.
  apply Q2Qc_eq_iff.
  rewrite Znat.Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus; reflexivity.
Qed.

(* --- the derivative --- *)
Fixpoint qderiv_aux (p : qpoly) (k : nat) : qpoly :=
  match p with
  | [] => []
  | c :: p' => (qnat k * c) :: qderiv_aux p' (S k)
  end.

Definition qderiv (p : qpoly) : qpoly :=
  match p with [] => [] | _ :: p' => qderiv_aux p' 1 end.

Lemma qderiv_aux_shift : forall p k x,
  qeval (qderiv_aux p (S k)) x = qeval (qderiv_aux p k) x + qeval p x.
Proof.
  induction p as [|c p' IH]; intros k x; [ simpl; ring | ].
  cbn [qderiv_aux qeval]; rewrite qnat_S, (IH (S k) x); ring.
Qed.

Lemma qderiv_aux_add : forall p q k x,
  qeval (qderiv_aux (qadd p q) k) x
  = qeval (qderiv_aux p k) x + qeval (qderiv_aux q k) x.
Proof.
  induction p as [|a p IH]; intros [|b q] k x; simpl; try ring.
  cbn [qderiv_aux qeval]; rewrite (IH q (S k) x); ring.
Qed.

Lemma qderiv_aux_scale : forall c p k x,
  qeval (qderiv_aux (qscale c p) k) x = c * qeval (qderiv_aux p k) x.
Proof.
  intros c p k x; revert k; induction p as [|a p IH]; intro k; [ simpl; ring | ].
  cbn [qscale map qderiv_aux qeval]; change (map (Qcmult c) p) with (qscale c p).
  rewrite (IH (S k)); ring.
Qed.

Lemma qderiv_cons_eval : forall c p' x,
  qeval (qderiv (c :: p')) x = qeval p' x + x * qeval (qderiv p') x.
Proof.
  intros c p' x; destruct p' as [|d p'']; [ simpl; ring | ].
  cbn [qderiv qderiv_aux qeval]; rewrite qnat_1.
  rewrite (qderiv_aux_shift p'' 1 x); ring.
Qed.

(* qderiv is additive: handled uniformly via qderiv_aux_add *)
Lemma qderiv_add_eval : forall p q x,
  qeval (qderiv (qadd p q)) x = qeval (qderiv p) x + qeval (qderiv q) x.
Proof.
  intros [|a p] [|b q] x; try (simpl; ring).
  cbn [qadd qderiv]; apply (qderiv_aux_add p q 1 x).
Qed.

Lemma qderiv_scale_eval : forall c p x,
  qeval (qderiv (qscale c p)) x = c * qeval (qderiv p) x.
Proof.
  intros c [|a p] x; [ simpl; ring | ].
  cbn [qscale map qderiv]; change (map (Qcmult c) p) with (qscale c p).
  apply (qderiv_aux_scale c p 1 x).
Qed.

Theorem qderiv_mul_eval : forall p q x,
  qeval (qderiv (qmul p q)) x
  = qeval (qderiv p) x * qeval q x + qeval p x * qeval (qderiv q) x.
Proof.
  induction p as [|c p' IH]; intros q x; [ simpl; ring | ].
  cbn [qmul]; rewrite qderiv_add_eval, qderiv_scale_eval.
  rewrite (qderiv_cons_eval 0 (qmul p' q) x), qeval_mul, (IH q x).
  rewrite (qderiv_cons_eval c p' x).
  change (qeval (c :: p') x) with (c + x * qeval p' x); ring.
Qed.

(* --- qderiv respects functional equality (via coeff-PIT) --- *)
Lemma qcoeff_qderiv_aux : forall p k i, qcoeff (qderiv_aux p k) i = qnat (k + i) * qcoeff p i.
Proof.
  induction p as [|c p' IH]; intros k i.
  - rewrite qcoeff_nil; simpl; rewrite qcoeff_nil; ring.
  - destruct i as [|i]; unfold qcoeff; simpl.
    + rewrite Nat.add_0_r; reflexivity.
    + change (nth i (qderiv_aux p' (S k)) 0) with (qcoeff (qderiv_aux p' (S k)) i).
      rewrite (IH (S k) i); replace (S k + i)%nat with (k + S i)%nat by lia; reflexivity.
Qed.

Lemma qcoeff_qderiv : forall p i, qcoeff (qderiv p) i = qnat (S i) * qcoeff p (S i).
Proof.
  intros [|c p'] i.
  - rewrite !qcoeff_nil; ring.
  - unfold qderiv; rewrite qcoeff_qderiv_aux.
    replace (1 + i)%nat with (S i) by lia; reflexivity.
Qed.

Lemma qcoeff_ext_eval : forall p q,
  (forall i, qcoeff p i = qcoeff q i) -> forall x, qeval p x = qeval q x.
Proof.
  induction p as [|a p IH]; intros [|b q] H x; simpl; try reflexivity.
  - assert (H0 : forall j, qcoeff q j = 0)
      by (intro j; change (qcoeff q j) with (qcoeff (b :: q) (S j));
          rewrite <- (H (S j)); apply qcoeff_nil).
    rewrite (qeval_all_zero q H0 x).
    pose proof (H 0%nat) as H1; unfold qcoeff in H1; simpl in H1; rewrite <- H1; ring.
  - assert (H0 : forall j, qcoeff p j = 0)
      by (intro j; change (qcoeff p j) with (qcoeff (a :: p) (S j));
          rewrite (H (S j)); apply qcoeff_nil).
    rewrite (qeval_all_zero p H0 x).
    pose proof (H 0%nat) as H1; unfold qcoeff in H1; simpl in H1; rewrite H1; ring.
  - rewrite (IH q (fun j => H (S j)) x).
    pose proof (H 0%nat) as H1; unfold qcoeff in H1; simpl in H1; rewrite H1; ring.
Qed.

Lemma qeval_ext_coeff : forall p q,
  (forall x, qeval p x = qeval q x) -> forall i, qcoeff p i = qcoeff q i.
Proof.
  intros p q H i.
  assert (Hz : forall x, qeval (qsub p q) x = 0) by (intro x; rewrite qeval_sub, H; ring).
  pose proof (qnorm_all_zero _ (qeval_zero_norm _ Hz) i) as Hc.
  rewrite qcoeff_sub in Hc.
  replace (qcoeff p i) with (qcoeff p i - qcoeff q i + qcoeff q i) by ring.
  rewrite Hc; ring.
Qed.

Theorem qderiv_resp_eval : forall p q,
  (forall x, qeval p x = qeval q x) -> forall x, qeval (qderiv p) x = qeval (qderiv q) x.
Proof.
  intros p q H; apply qcoeff_ext_eval; intro i.
  rewrite !qcoeff_qderiv, (qeval_ext_coeff p q H (S i)); reflexivity.
Qed.

(* --- derivative of X^n − 1 --- *)
Lemma qeval_qderiv_qmonom : forall n x, qeval (qderiv (qmonom n)) x = qnat n * x ^ (Nat.pred n).
Proof.
  induction n as [|n IH]; intro x.
  - change (qnat 0) with 0; simpl; ring.
  - cbn [qmonom]; rewrite (qderiv_cons_eval 0 (qmonom n) x), qeval_monom, IH, qnat_S.
    destruct n as [|n'].
    + change (qnat 0) with 0; simpl; ring.
    + cbn [Nat.pred]; change (x ^ S n') with (x * x ^ n'); ring.
Qed.

Theorem qeval_qderiv_Xn1 : forall n x,
  qeval (qderiv (qXn1 n)) x = qnat n * x ^ (Nat.pred n).
Proof.
  intros n x; unfold qXn1; rewrite qderiv_add_eval, qeval_qderiv_qmonom.
  unfold qconst; cbn [qderiv]; simpl; ring.
Qed.

Print Assumptions qderiv_mul_eval.
Print Assumptions qderiv_resp_eval.
Print Assumptions qeval_qderiv_Xn1.

(* ================================================================= *)
(*  END QPolyDeriv.v                                                 *)
(*  Formal derivative in ℚ[X]: product rule, respects functional      *)
(*  equality, and (X^n−1)′ = n·X^{n−1}.  Closed under the global      *)
(*  context (axiom-free).                                            *)
(* ================================================================= *)
