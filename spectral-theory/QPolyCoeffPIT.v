(* ================================================================= *)
(*  QPolyCoeffPIT.v                                                  *)
(*                                                                    *)
(*  COEFFICIENT-FORM POLYNOMIAL IDENTITY THEOREM in ℚ[X] (brick 5c). *)
(*                                                                    *)
(*    (∀x, qeval p x = 0)  →  qnorm p = []                          *)
(*                                                                    *)
(*  i.e. a polynomial that vanishes as a FUNCTION has all-zero        *)
(*  coefficients.  This is the bridge between the eval-based ℚ[X]     *)
(*  layer and coefficient-level reasoning (needed to differentiate    *)
(*  the identity X^n−1 = h²·k for squarefreeness).                   *)
(*                                                                    *)
(*  Proof: strong step — the constant term is p(0) = 0; then          *)
(*  x·(tail)(x) ≡ 0, so the tail vanishes at every nonzero point;     *)
(*  supplying `deg(tail)+1` distinct nonzero points `qnat(S k)`, the  *)
(*  functional PIT (QPolyPIT.poly_roots_eval) makes the tail vanish   *)
(*  everywhere, and structural recursion finishes.  AXIOM-FREE.      *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyDeg QPolyGcd QPolyRoot QPolyPIT.
Open Scope Qc_scope.

(* distinct nonzero rationals from naturals *)
Definition qnat (k : nat) : Qc := Q2Qc (inject_Z (Z.of_nat k)).

Lemma qnat_inj : forall i j, qnat i = qnat j -> i = j.
Proof.
  intros i j H; unfold qnat in H; apply Q2Qc_eq_iff in H.
  unfold Qeq in H; simpl in H; apply Znat.Nat2Z.inj; lia.
Qed.

Lemma qnat_0 : qnat 0 = 0.
Proof. reflexivity. Qed.

Lemma qnat_Sk_nz : forall k, qnat (S k) <> 0.
Proof. intros k H; rewrite <- qnat_0 in H; apply qnat_inj in H; discriminate. Qed.

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hinj Hnd; simpl; [ constructor | ].
  inversion Hnd as [| ? ? Hna Hndl]; subst; constructor.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Hfy Hyin]].
    apply Hna; rewrite (Hinj a y (or_introl eq_refl) (or_intror Hyin) (eq_sym Hfy)); exact Hyin.
  - apply IH; [ intros x y Hx Hy; apply Hinj; right; assumption | exact Hndl ].
Qed.

Theorem qeval_zero_norm : forall p, (forall x, qeval p x = 0) -> qnorm p = [].
Proof.
  induction p as [|c p' IH]; intro H; [ reflexivity | ].
  assert (Hc : c = 0).
  { pose proof (H 0) as H0; simpl in H0; rewrite Qcmult_0_l, Qcplus_0_r in H0; exact H0. }
  assert (Hxp' : forall x, x * qeval p' x = 0).
  { intro x; pose proof (H x) as Hx; simpl in Hx; rewrite Hc, Qcplus_0_l in Hx; exact Hx. }
  assert (Hp' : forall x, qeval p' x = 0).
  { set (pts := map (fun k => qnat (S k)) (seq 0 (S (length p')))).
    apply (poly_roots_eval (length p') p' (qdegle_length p') pts).
    - apply NoDup_map_inj; [ intros x y _ _ Hxy; apply qnat_inj in Hxy; lia | apply seq_NoDup ].
    - unfold pts; rewrite length_map, length_seq; lia.
    - intros a Hain; unfold pts in Hain; apply in_map_iff in Hain.
      destruct Hain as [k [Hk _]]; subst a.
      pose proof (Hxp' (qnat (S k))) as Hq; apply Qcmult_integral in Hq.
      destruct Hq as [Hz | Hz]; [ exfalso; apply (qnat_Sk_nz k); exact Hz | exact Hz ]. }
  cbn [qnorm]; rewrite (IH Hp'); unfold qnonzero.
  destruct (Qc_eq_dec c 0) as [ | Hnz ]; [ reflexivity | destruct (Hnz Hc) ].
Qed.

Print Assumptions qeval_zero_norm.

(* ================================================================= *)
(*  END QPolyCoeffPIT.v                                              *)
(*  Coefficient-form polynomial identity theorem: eval ≡ 0 ⟹         *)
(*  qnorm = [].  The bridge from functional to coefficient reasoning  *)
(*  in ℚ[X].  Closed under the global context (axiom-free).          *)
(* ================================================================= *)
