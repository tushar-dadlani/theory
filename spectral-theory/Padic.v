(* ================================================================= *)
(*  Padic.v                                                           *)
(*                                                                    *)
(*  The p-adic ULTRAMETRIC (non-archimedean absolute value), over Q,  *)
(*  axiom-free, wired to BiView.                                       *)
(*                                                                    *)
(*  For a prime p, the p-adic absolute value of an element of         *)
(*  valuation v is  |x|_p = p^{-v}, which is RATIONAL (a power of      *)
(*  1/p).  So a genuine non-archimedean norm and its ultrametric       *)
(*  structure live entirely over Q -- no Reals, no completion, no      *)
(*  topology library needed.                                          *)
(*                                                                    *)
(*  We index by the valuation v : nat (the p-adic integers side,       *)
(*  v >= 0 = "how divisible by p"), which IS BiView's global           *)
(*  coordinate.  We prove:                                            *)
(*    - pabs positive, pabs 0 = 1 (units have norm 1);                 *)
(*    - MULTIPLICATIVE: pabs (v+w) = pabs v * pabs w  (valuation-      *)
(*      additivity -> norm-multiplicativity);                          *)
(*    - ANTITONE: larger valuation = smaller norm (closer to 0);       *)
(*    - the ULTRAMETRIC max-law: pabs is a decreasing exponential of   *)
(*      the valuation, so a sum (whose valuation is >= the min) has    *)
(*      norm <= max of the two norms -- the strong triangle law.       *)
(*                                                                    *)
(*  WIRING TO BiView: pabs is the NON-ARCHIMEDEAN view of the same     *)
(*  valuation that BiView.alpha views archimedeanly; they move in      *)
(*  OPPOSITE directions (alpha increases, pabs decreases) -- the two   *)
(*  completions (real / p-adic) of one arithmetic object.             *)
(* ================================================================= *)

From Stdlib Require Import QArith Qminmax Lqa ZArith PArith Lia.
Require Import BiView.
Open Scope Q_scope.

Section PadicNorm.

Variable p : positive.
Hypothesis Hp : (2 <= Z.pos p)%Z.   (* p >= 2 (a prime; the ultrametric needs only >= 2) *)

(* p^v as a positive number *)
Fixpoint ppow (v : nat) : positive :=
  match v with O => 1%positive | S v' => (p * ppow v')%positive end.

(* the p-adic absolute value of an element of valuation v: |x|_p = p^{-v} *)
Definition pabs (v : nat) : Q := 1 # ppow v.

Lemma ppow_mult : forall v w, (ppow (v + w) = ppow v * ppow w)%positive.
Proof.
  induction v as [|v IH]; intro w; simpl.
  - reflexivity.
  - rewrite IH, Pos.mul_assoc; reflexivity.
Qed.

Lemma ppow_le : forall v w, (v <= w)%nat -> (Z.pos (ppow v) <= Z.pos (ppow w))%Z.
Proof.
  intros v w H; induction H as [|w Hw IH].
  - lia.
  - simpl (ppow (S w)); rewrite Pos2Z.inj_mul; nia.
Qed.

Lemma pabs_pos : forall v, 0 < pabs v.
Proof. intro v; unfold pabs, Qlt; simpl; lia. Qed.

Lemma pabs_one : pabs 0 == 1.
Proof. unfold pabs; simpl; reflexivity. Qed.

(* MULTIPLICATIVITY: valuations add, norms multiply *)
Theorem pabs_mult : forall v w, pabs (v + w) == pabs v * pabs w.
Proof. intros v w; unfold pabs; rewrite ppow_mult; reflexivity. Qed.

(* ANTITONE: larger valuation (more divisible by p) = smaller norm *)
Theorem pabs_antitone : forall v w, (v <= w)%nat -> pabs w <= pabs v.
Proof.
  intros v w H; unfold pabs, Qle; simpl; pose proof (ppow_le v w H); lia.
Qed.

(* the min-valuation has the max norm *)
Lemma pabs_min : forall v w, pabs (Nat.min v w) == Qmax (pabs v) (pabs w).
Proof.
  intros v w; destruct (Nat.le_ge_cases v w) as [H | H].
  - rewrite Nat.min_l by exact H.
    rewrite Q.max_l by (apply pabs_antitone; exact H); reflexivity.
  - rewrite Nat.min_r by exact H.
    rewrite Q.max_r by (apply pabs_antitone; exact H); reflexivity.
Qed.

(* THE ULTRAMETRIC (strong triangle) INEQUALITY: an element whose      *)
(* valuation is >= min(v,w) -- e.g. a sum of elements of valuations    *)
(* v and w -- has norm <= max of the two norms.                        *)
Theorem pabs_ultrametric : forall v w u,
  (Nat.min v w <= u)%nat -> pabs u <= Qmax (pabs v) (pabs w).
Proof.
  intros v w u H.
  rewrite <- pabs_min.
  apply pabs_antitone; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(* WIRING TO BiView: pabs is the non-archimedean view of the           *)
(* valuation, moving OPPOSITE to BiView.alpha (the archimedean view).  *)
(* ----------------------------------------------------------------- *)

Theorem arch_padic_opposite : forall v w, (v <= w)%nat ->
  alpha (Z.of_nat v) <= alpha (Z.of_nat w)   (* archimedean view increases *)
  /\ pabs w <= pabs v.                        (* p-adic view decreases *)
Proof.
  intros v w H; split.
  - apply alpha_monotone; lia.
  - apply pabs_antitone; exact H.
Qed.

Theorem padic_ultrametric :
  (forall v, 0 < pabs v)
  /\ pabs 0 == 1
  /\ (forall v w, pabs (v + w) == pabs v * pabs w)
  /\ (forall v w, (v <= w)%nat -> pabs w <= pabs v)
  /\ (forall v w u, (Nat.min v w <= u)%nat -> pabs u <= Qmax (pabs v) (pabs w))
  /\ (forall v w, (v <= w)%nat ->
        alpha (Z.of_nat v) <= alpha (Z.of_nat w) /\ pabs w <= pabs v).
Proof.
  split; [ exact pabs_pos | ].
  split; [ exact pabs_one | ].
  split; [ exact pabs_mult | ].
  split; [ exact pabs_antitone | ].
  split; [ exact pabs_ultrametric | exact arch_padic_opposite ].
Qed.

End PadicNorm.

Print Assumptions padic_ultrametric.

(* ================================================================= *)
(*  END Padic.v                                                       *)
(*  A genuine non-archimedean (p-adic) ultrametric over Q, axiom-free, *)
(*  as the non-archimedean companion of BiView's archimedean view.     *)
(* ================================================================= *)
