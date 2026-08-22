(* ================================================================= *)
(*  LipCalc.v  --  a Lipschitz-and-bounded calculus on an interval.    *)
(*                                                                    *)
(*    BddOn f A B M  :=  |f x| <= M            on [A,B]               *)
(*    LipOn f A B K  :=  |f x - f y| <= K|x-y| on [A,B]               *)
(*                                                                    *)
(*  Stage 4c plumbing.  MidpointQuad.midpoint_single asks for a        *)
(*  Lipschitz bound on the DERIVATIVE of the integrand, and the        *)
(*  integrand Psi(e^x) e^{x/4} cos(tx/2) is a three-fold product whose *)
(*  derivative is a sum of three such products.  Discharging that by   *)
(*  hand each time would be six near-identical MVT arguments; the      *)
(*  closure rules below do it once.                                    *)
(*                                                                    *)
(*  The only nontrivial rule is lip_mult, and it is the usual          *)
(*  identity                                                          *)
(*     f(x)g(x) - f(y)g(y) = f(x)(g(x)-g(y)) + g(y)(f(x)-f(y)),        *)
(*  which is why a product needs BOTH factors bounded AND both         *)
(*  Lipschitz: the constant is M1 K2 + M2 K1.  lip_of_deriv is the     *)
(*  bridge from analysis (MVT_cor2) into this algebra, and after it    *)
(*  nothing below reasons about derivatives again.                     *)
(*                                                                    *)
(*  Axiom-clean; no dependence on the rest of the tree.                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Definition BddOn (f : R -> R) (A B M : R) : Prop :=
  forall x, A <= x <= B -> Rabs (f x) <= M.
Definition LipOn (f : R -> R) (A B K : R) : Prop :=
  forall x y, A <= x <= B -> A <= y <= B -> Rabs (f x - f y) <= K * Rabs (x - y).

(* ----------------------------------------------------------------- *)
(*  A.  the bridge from calculus                                      *)
(* ----------------------------------------------------------------- *)
Lemma lip_of_deriv : forall f f' A B M,
  (forall x, A <= x <= B -> derivable_pt_lim f x (f' x)) ->
  BddOn f' A B M -> LipOn f A B M.
Proof.
  intros f f' A B M Hd Hb.
  assert (Hgen : forall p q, A <= p <= B -> A <= q <= B -> p < q ->
    Rabs (f p - f q) <= M * Rabs (p - q)).
  { intros p q Hp Hq Hpq.
    destruct (MVT_cor2 f f' p q Hpq
                (fun c Hc => Hd c (conj (Rle_trans _ _ _ (proj1 Hp) (proj1 Hc))
                                        (Rle_trans _ _ _ (proj2 Hc) (proj2 Hq)))))
      as [c [Hc Hcr]].
    assert (Hcin : A <= c <= B) by lra.
    replace (f p - f q) with (- (f q - f p)) by ring.
    rewrite Rabs_Ropp, Hc, Rabs_mult.
    replace (Rabs (p - q)) with (Rabs (q - p))
      by (rewrite <- (Rabs_Ropp (q - p)); f_equal; ring).
    apply Rmult_le_compat_r; [ apply Rabs_pos | apply Hb; exact Hcin ]. }
  intros x y Hx Hy.
  destruct (Rtotal_order x y) as [H | [H | H]].
  - apply Hgen; assumption.
  - subst y. replace (f x - f x) with 0 by ring. rewrite Rabs_R0.
    apply Rmult_le_pos; [ | apply Rabs_pos ].
    apply Rle_trans with (Rabs (f' x)); [ apply Rabs_pos | apply Hb; exact Hx ].
  - replace (f x - f y) with (- (f y - f x)) by ring. rewrite Rabs_Ropp.
    replace (Rabs (x - y)) with (Rabs (y - x))
      by (rewrite <- (Rabs_Ropp (y - x)); f_equal; ring).
    apply Hgen; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  closure rules                                                 *)
(* ----------------------------------------------------------------- *)
Lemma bdd_nonneg : forall f A B M x, A <= x <= B -> BddOn f A B M -> 0 <= M.
Proof.
  intros f A B M x Hx Hb.
  apply Rle_trans with (Rabs (f x)); [ apply Rabs_pos | apply Hb; exact Hx ].
Qed.

Lemma lip_const : forall c A B, LipOn (fun _ => c) A B 0.
Proof.
  intros c A B x y _ _. replace (c - c) with 0 by ring.
  rewrite Rabs_R0. pose proof (Rabs_pos (x - y)). lra.
Qed.

Lemma bdd_const : forall c A B, BddOn (fun _ => c) A B (Rabs c).
Proof. intros c A B x _. apply Rle_refl. Qed.

Lemma lip_scal : forall f A B K c, 0 <= K -> LipOn f A B K ->
  LipOn (fun x => c * f x) A B (Rabs c * K).
Proof.
  intros f A B K c HK HL x y Hx Hy.
  replace (c * f x - c * f y) with (c * (f x - f y)) by ring.
  rewrite Rabs_mult.
  assert (H := HL x y Hx Hy).
  assert (Hc : 0 <= Rabs c) by apply Rabs_pos.
  replace (Rabs c * K * Rabs (x - y)) with (Rabs c * (K * Rabs (x - y))) by ring.
  apply Rmult_le_compat_l; assumption.
Qed.

Lemma bdd_scal : forall f A B M c, BddOn f A B M ->
  BddOn (fun x => c * f x) A B (Rabs c * M).
Proof.
  intros f A B M c Hb x Hx. replace (c * f x) with (c * f x) by ring.
  rewrite Rabs_mult. apply Rmult_le_compat_l; [ apply Rabs_pos | apply Hb; exact Hx ].
Qed.

Lemma lip_plus : forall f g A B K1 K2,
  LipOn f A B K1 -> LipOn g A B K2 -> LipOn (fun x => f x + g x) A B (K1 + K2).
Proof.
  intros f g A B K1 K2 Hf Hg x y Hx Hy.
  replace (f x + g x - (f y + g y)) with ((f x - f y) + (g x - g y)) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ].
  pose proof (Hf x y Hx Hy). pose proof (Hg x y Hx Hy). lra.
Qed.

Lemma bdd_plus : forall f g A B M1 M2,
  BddOn f A B M1 -> BddOn g A B M2 -> BddOn (fun x => f x + g x) A B (M1 + M2).
Proof.
  intros f g A B M1 M2 Hf Hg x Hx.
  eapply Rle_trans; [ apply Rabs_triang | ].
  pose proof (Hf x Hx). pose proof (Hg x Hx). lra.
Qed.

Lemma bdd_mult : forall f g A B M1 M2, 0 <= M1 ->
  BddOn f A B M1 -> BddOn g A B M2 -> BddOn (fun x => f x * g x) A B (M1 * M2).
Proof.
  intros f g A B M1 M2 HM1 Hf Hg x Hx.
  rewrite Rabs_mult.
  assert (H1 := Hf x Hx). assert (H2 := Hg x Hx).
  pose proof (Rabs_pos (f x)). pose proof (Rabs_pos (g x)).
  apply Rle_trans with (M1 * Rabs (g x)).
  - apply Rmult_le_compat_r; assumption.
  - apply Rmult_le_compat_l; assumption.
Qed.

Lemma lip_mult : forall f g A B M1 M2 K1 K2,
  0 <= M1 -> 0 <= M2 -> 0 <= K1 -> 0 <= K2 ->
  BddOn f A B M1 -> BddOn g A B M2 ->
  LipOn f A B K1 -> LipOn g A B K2 ->
  LipOn (fun x => f x * g x) A B (M1 * K2 + M2 * K1).
Proof.
  intros f g A B M1 M2 K1 K2 HM1 HM2 HK1 HK2 Hbf Hbg Hlf Hlg x y Hx Hy.
  replace (f x * g x - f y * g y)
    with (f x * (g x - g y) + g y * (f x - f y)) by ring.
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult.
  assert (Hd : 0 <= Rabs (x - y)) by apply Rabs_pos.
  assert (T1 : Rabs (f x) * Rabs (g x - g y) <= M1 * (K2 * Rabs (x - y))).
  { apply Rmult_le_compat.
    - apply Rabs_pos.
    - apply Rabs_pos.
    - apply Hbf; exact Hx.
    - apply Hlg; assumption. }
  assert (T2 : Rabs (g y) * Rabs (f x - f y) <= M2 * (K1 * Rabs (x - y))).
  { apply Rmult_le_compat.
    - apply Rabs_pos.
    - apply Rabs_pos.
    - apply Hbg; exact Hy.
    - apply Hlf; assumption. }
  lra.
Qed.

Lemma lip_comp : forall (h f : R -> R) A B A' B' K1 K2,
  0 <= K1 ->
  (forall x, A <= x <= B -> A' <= h x <= B') ->
  LipOn h A B K2 -> LipOn f A' B' K1 ->
  LipOn (fun x => f (h x)) A B (K1 * K2).
Proof.
  intros h f A B A' B' K1 K2 HK1 Hrng Hlh Hlf x y Hx Hy.
  eapply Rle_trans; [ apply Hlf; [ apply Hrng; exact Hx | apply Hrng; exact Hy ] | ].
  assert (H := Hlh x y Hx Hy).
  replace (K1 * K2 * Rabs (x - y)) with (K1 * (K2 * Rabs (x - y))) by ring.
  apply Rmult_le_compat_l; assumption.
Qed.

Lemma bdd_comp : forall (h f : R -> R) A B A' B' M,
  (forall x, A <= x <= B -> A' <= h x <= B') ->
  BddOn f A' B' M -> BddOn (fun x => f (h x)) A B M.
Proof. intros h f A B A' B' M Hrng Hb x Hx. apply Hb, Hrng, Hx. Qed.

(* monotone weakening, for reconciling constants at the end *)
Lemma lip_weaken : forall f A B K K', K <= K' -> LipOn f A B K -> LipOn f A B K'.
Proof.
  intros f A B K K' Hle HL x y Hx Hy.
  eapply Rle_trans; [ apply HL; assumption | ].
  apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hle ].
Qed.

Lemma bdd_weaken : forall f A B M M', M <= M' -> BddOn f A B M -> BddOn f A B M'.
Proof. intros f A B M M' Hle Hb x Hx. eapply Rle_trans; [ apply Hb; exact Hx | exact Hle ]. Qed.

Print Assumptions lip_of_deriv.
Print Assumptions lip_mult.
Print Assumptions lip_comp.
