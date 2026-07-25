(* ================================================================= *)
(*  QPolyDeg.v                                                       *)
(*                                                                    *)
(*  DEGREE MACHINERY FOR ℚ[X] (brick 3a of the ℚ[X] layer).         *)
(*                                                                    *)
(*  The Euclidean-algorithm gcd needs the ACTUAL degree and leading  *)
(*  coefficient of a polynomial (to know where to divide and to see  *)
(*  the remainder's degree drop).  `qnorm` strips trailing zeros;     *)
(*  `qdeg p := length (qnorm p) − 1`; `qlead p := qcoeff p (qdeg p)`. *)
(*  Key facts: coefficients are unchanged by `qnorm`, the leading     *)
(*  coefficient of a nonzero polynomial is nonzero, and a degree      *)
(*  bound really bounds the degree.  AXIOM-FREE.                     *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly.
Open Scope Qc_scope.

Definition qnonzero (c : Qc) : bool := if Qc_eq_dec c 0 then false else true.

Fixpoint qnorm (p : qpoly) : qpoly :=
  match p with
  | [] => []
  | c :: p' =>
      match qnorm p' with
      | [] => if qnonzero c then [c] else []
      | q => c :: q
      end
  end.

Definition qdeg (p : qpoly) : nat := Nat.pred (length (qnorm p)).
Definition qlead (p : qpoly) : Qc := qcoeff p (qdeg p).

(* trailing zeros don't change any coefficient *)
Lemma qcoeff_qnorm : forall p i, qcoeff (qnorm p) i = qcoeff p i.
Proof.
  induction p as [|c p' IH]; intro i; [ reflexivity | ].
  cbn [qnorm]; remember (qnorm p') as np eqn:E.
  destruct np as [|a q].
  - assert (Hz : forall j, qcoeff p' j = 0)
      by (intro j; rewrite <- (IH j); apply qcoeff_nil).
    unfold qcoeff in Hz.
    destruct (qnonzero c) eqn:Ec; unfold qcoeff; destruct i as [|i]; simpl.
    + reflexivity.
    + rewrite Hz; destruct i; reflexivity.
    + unfold qnonzero in Ec; destruct (Qc_eq_dec c 0) as [Hc | Hc];
        [ symmetry; exact Hc | discriminate Ec ].
    + rewrite Hz; destruct i; reflexivity.
  - unfold qcoeff; destruct i as [|i]; simpl; [ reflexivity | ].
    unfold qcoeff in IH; apply (IH i).
Qed.

Lemma qnorm_all_zero : forall p, qnorm p = [] -> forall i, qcoeff p i = 0.
Proof.
  intros p H i; rewrite <- qcoeff_qnorm, H; unfold qcoeff; destruct i; reflexivity.
Qed.

(* the degree bound is genuine: coefficients above qdeg vanish *)
Lemma qdegle_above : forall p, qdegle p (qdeg p).
Proof.
  intros p i Hi; rewrite <- qcoeff_qnorm; unfold qcoeff, qdeg in *.
  apply nth_overflow; lia.
Qed.

(* the leading coefficient of the normal form is its last entry, nonzero *)
Lemma qnorm_top_nz : forall p, qnorm p <> [] ->
  qcoeff (qnorm p) (Nat.pred (length (qnorm p))) <> 0.
Proof.
  induction p as [|c p' IH]; intro H; [ destruct (H eq_refl) | ].
  cbn [qnorm] in *; destruct (qnorm p') as [|a q] eqn:E.
  - unfold qnonzero in *; destruct (Qc_eq_dec c 0) as [Hc | Hc]; [ destruct (H eq_refl) | ].
    simpl; unfold qcoeff; simpl; exact Hc.
  - simpl in *; unfold qcoeff in *; simpl.
    specialize (IH ltac:(discriminate)); exact IH.
Qed.

Lemma qlead_nonzero : forall p, qnorm p <> [] -> qlead p <> 0.
Proof.
  intros p H; unfold qlead, qdeg.
  rewrite <- (qcoeff_qnorm p (Nat.pred (length (qnorm p)))).
  apply qnorm_top_nz; exact H.
Qed.

(* a degree bound bounds the actual degree *)
Lemma qdegle_qdeg : forall p n, qdegle p n -> (qdeg p <= n)%nat.
Proof.
  intros p n H; destruct (qnorm p) as [|c q] eqn:E.
  - unfold qdeg; rewrite E; simpl; lia.
  - destruct (le_gt_dec (qdeg p) n) as [Hle | Hgt]; [ exact Hle | exfalso ].
    apply (qlead_nonzero p); [ rewrite E; discriminate | ].
    unfold qlead; apply H; exact Hgt.
Qed.

Print Assumptions qlead_nonzero.
Print Assumptions qdegle_qdeg.

(* ================================================================= *)
(*  END QPolyDeg.v                                                   *)
(*  qnorm / qdeg / qlead for ℚ[X], with: coefficients unchanged by    *)
(*  normalization, leading coefficient of a nonzero polynomial is     *)
(*  nonzero, and a degree bound bounds the degree.  Foundation for    *)
(*  the ℚ[X] gcd.  Closed under the global context (axiom-free).     *)
(* ================================================================= *)
