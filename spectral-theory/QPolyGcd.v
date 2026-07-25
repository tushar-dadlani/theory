(* ================================================================= *)
(*  QPolyGcd.v                                                       *)
(*                                                                    *)
(*  THE EXTENDED EUCLIDEAN ALGORITHM IN ℚ[X] (brick 3b).            *)
(*                                                                    *)
(*  `qeuclid fuel f g` returns (h, u, v) with                        *)
(*      u·f + v·g = h,      h | f,      h | g,                       *)
(*  provided the fuel exceeds deg g (so the recursion reaches a base).*)
(*  h is a COMMON DIVISOR carrying a Bézout combination.  When f, g   *)
(*  are coprime (every common divisor is a nonzero constant) this     *)
(*  forces h constant, giving a Bézout identity `u·f + v·g = 1` after  *)
(*  scaling — the tool for the coprimality of cyclotomic factors.     *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyDeg.
Open Scope Qc_scope.

(* ----------------------------------------------------------------- *)
(*  Divisibility in ℚ[X]                                             *)
(* ----------------------------------------------------------------- *)
Definition qdivides (p q : qpoly) : Prop :=
  exists r, forall x, qeval q x = qeval p x * qeval r x.

Lemma qdivides_refl : forall p, qdivides p p.
Proof. intro p; exists [1]; intro x; simpl; ring. Qed.

Lemma qdivides_one : forall p, qdivides [1] p.
Proof. intro p; exists p; intro x; simpl; ring. Qed.

Lemma qdivides_zero : forall p g, (forall x, qeval g x = 0) -> qdivides p g.
Proof. intros p g H; exists []; intro x; rewrite H; simpl; ring. Qed.

Lemma qdivides_lincomb : forall h g r q f,
  qdivides h g -> qdivides h r ->
  (forall x, qeval f x = qeval q x * qeval g x + qeval r x) ->
  qdivides h f.
Proof.
  intros h g r q f [a Ha] [b Hb] Hf.
  exists (qadd (qmul q a) b); intro x.
  rewrite Hf, Ha, Hb, qeval_add, qeval_mul; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Evaluation of the zero / normalized polynomial                   *)
(* ----------------------------------------------------------------- *)
Lemma qeval_all_zero : forall p, (forall i, qcoeff p i = 0) -> forall x, qeval p x = 0.
Proof.
  induction p as [|c p' IH]; intros H x; [ reflexivity | ].
  simpl; rewrite (IH (fun i => H (S i)) x).
  assert (Hc : c = 0) by (specialize (H 0%nat); unfold qcoeff in H; simpl in H; exact H).
  rewrite Hc; ring.
Qed.

Lemma qeval_qnorm : forall p x, qeval (qnorm p) x = qeval p x.
Proof.
  induction p as [|c p' IH]; intro x; [ reflexivity | ].
  cbn [qnorm]; remember (qnorm p') as np eqn:E; destruct np as [|a q].
  - assert (Hp' : qeval p' x = 0) by (rewrite <- (IH x); reflexivity).
    destruct (qnonzero c) eqn:Ec; simpl.
    + rewrite Hp'; ring.
    + unfold qnonzero in Ec; destruct (Qc_eq_dec c 0) as [Hc | ];
        [ rewrite Hp', Hc; ring | discriminate ].
  - transitivity (c + x * qeval (a :: q) x); [ reflexivity | ].
    rewrite (IH x); reflexivity.
Qed.

Lemma qeval_qnorm_nil : forall g, qnorm g = [] -> forall x, qeval g x = 0.
Proof.
  intros g H x; rewrite <- qeval_qnorm, H; reflexivity.
Qed.

Lemma qdegle_length : forall f, qdegle f (length f).
Proof. intros f i Hi; unfold qcoeff; apply nth_overflow; lia. Qed.

(* ----------------------------------------------------------------- *)
(*  The extended Euclidean algorithm                                 *)
(* ----------------------------------------------------------------- *)
Fixpoint qeuclid (fuel : nat) (f g : qpoly) : qpoly * qpoly * qpoly :=
  match fuel with
  | O => (f, [1], [])
  | S fl =>
      match qnorm g with
      | [] => (f, [1], [])
      | c :: [] => ([1], [], [/ c])
      | _ =>
          let '(q, r) := qdivmod (length f) f g (qdeg g) (qlead g) in
          let '(hr, u', v') := qeuclid fl g r in
          (hr, v', qsub u' (qmul v' q))
      end
  end.

Lemma qeuclid_spec : forall fuel f g, (qdeg g < fuel)%nat ->
  let '(h, u, v) := qeuclid fuel f g in
  (forall x, qeval u x * qeval f x + qeval v x * qeval g x = qeval h x)
  /\ qdivides h f /\ qdivides h g.
Proof.
  induction fuel as [|fl IH]; intros f g Hlt; [ exfalso; lia | ].
  cbn [qeuclid]; destruct (qnorm g) as [|c [|a l]] eqn:Eg.
  - (* g = 0 *)
    split; [ | split ].
    + intro x; rewrite (qeval_qnorm_nil g Eg x); simpl; ring.
    + apply qdivides_refl.
    + apply qdivides_zero; apply qeval_qnorm_nil; exact Eg.
  - (* g nonzero constant c *)
    assert (Hcnz : qlead g <> 0) by (apply qlead_nonzero; rewrite Eg; discriminate).
    assert (Hqd0 : qdeg g = 0%nat) by (unfold qdeg; rewrite Eg; reflexivity).
    assert (Hgc : forall x, qeval g x = c).
    { intro x; rewrite <- qeval_qnorm, Eg; simpl; ring. }
    assert (Hc : c <> 0).
    { intro Hz; apply Hcnz; unfold qlead; rewrite Hqd0.
      rewrite <- (qcoeff_qnorm g 0), Eg; simpl; exact Hz. }
    split; [ | split ].
    + intro x; simpl; rewrite Hgc; field; exact Hc.
    + apply qdivides_one.
    + apply qdivides_one.
  - (* deg g >= 1 : divide and recurse *)
    assert (Hgnn : qnorm g <> []) by (rewrite Eg; discriminate).
    assert (Hqd1 : (1 <= qdeg g)%nat) by (unfold qdeg; rewrite Eg; simpl; lia).
    assert (Hlead : qlead g <> 0) by (apply qlead_nonzero; exact Hgnn).
    pose proof (qdivmod_spec g (qdeg g) (qlead g) Hqd1 Hlead eq_refl
                  (qdegle_above g) (length f) f (qdegle_length f)) as Hdm.
    destruct (qdivmod (length f) f g (qdeg g) (qlead g)) as [q r] eqn:Edm.
    cbn [fst snd] in Hdm; destruct Hdm as [Hfqr [Hrdeg _]].
    assert (Hrfl : (qdeg r < fl)%nat).
    { pose proof (qdegle_qdeg r (Nat.pred (qdeg g)) Hrdeg); lia. }
    specialize (IH g r Hrfl).
    destruct (qeuclid fl g r) as [[hr u'] v'] eqn:Eqe.
    cbn [fst snd] in IH |- *; destruct IH as [Hbez [Hhg Hhr]].
    split; [ | split ].
    + intro x; rewrite qeval_sub, qeval_mul.
      specialize (Hfqr x); specialize (Hbez x).
      rewrite Hfqr, <- Hbez; ring.
    + apply (qdivides_lincomb hr g r q f Hhg Hhr Hfqr).
    + exact Hhg.
Qed.

Print Assumptions qeuclid_spec.

(* ================================================================= *)
(*  END QPolyGcd.v                                                   *)
(*  Extended Euclidean algorithm in ℚ[X]: u·f + v·g = h with h a      *)
(*  common divisor of f and g.  Closed under the global context      *)
(*  (axiom-free).                                                    *)
(* ================================================================= *)
