(* ================================================================= *)
(*  HopfGroupAlgebra.v                                               *)
(*                                                                    *)
(*  THE FINITE GROUP ALGEBRA  k[ℤ/nℤ]  and its HOPF DUALITY with the  *)
(*  function algebra  k^{ℤ/nℤ}  — combinatorial, AXIOM-FREE.         *)
(*                                                                    *)
(*  Elements are functions ℤ/nℤ → ℤ (as `nat → Z`, indices taken      *)
(*  mod n).  The group algebra k[G] has:                              *)
(*     product   (a ⋆ b)_k = Σ_{i+j≡k} a_i b_j     (convolution)      *)
(*     unit      e_0                                                  *)
(*     coproduct Δ(e_g) = e_g ⊗ e_g                (diagonal)         *)
(*     counit    ε(a)   = Σ_g a_g                  (augmentation)     *)
(*     antipode  S(e_g) = e_{−g}                    (inversion)       *)
(*                                                                    *)
(*  The dual function algebra k^G (pointwise product) pairs with k[G] *)
(*  via ⟨a, φ⟩ = Σ_g a_g φ_g, and the fundamental DUALITY holds:      *)
(*     ⟨a ⋆ b, φ⟩ = Σ_{i,j} a_i b_j φ_{i+j}   (product ↔ coproduct)   *)
(*     ⟨a, φ·ψ⟩  = Σ_g a_g φ_g ψ_g            (coproduct ↔ product)   *)
(*  and the antipode axiom  m∘(S⊗id)∘Δ = η∘ε.                        *)
(*                                                                    *)
(*  No roots of unity / DFT (that route uses the classical Reals      *)
(*  axioms) — everything reduces to Fubini + a sifting lemma over the *)
(*  finite index set.  Closed under the global context (axiom-free).  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith Lia List.
Import ListNotations.
Open Scope Z_scope.

Section GroupAlgebra.
Variable n : nat.
Hypothesis Hn : (0 < n)%nat.

(* ================================================================= *)
(*  A small finite-sum toolkit                                        *)
(* ================================================================= *)
Definition sumf (l : list nat) (f : nat -> Z) : Z :=
  fold_right (fun k acc => f k + acc) 0%Z l.
Definition bigsum (f : nat -> Z) : Z := sumf (seq 0 n) f.

Lemma sumf_ext : forall l f g,
  (forall k, In k l -> f k = g k) -> sumf l f = sumf l g.
Proof.
  induction l as [|a l IH]; intros f g H; simpl; [ reflexivity | ].
  rewrite (H a (or_introl eq_refl)), (IH f g); [ reflexivity | ].
  intros k Hk; apply H; right; exact Hk.
Qed.

Lemma sumf_zero : forall l, sumf l (fun _ => 0%Z) = 0%Z.
Proof. induction l as [|a l IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma sumf_add : forall l f g,
  sumf l (fun k => f k + g k) = sumf l f + sumf l g.
Proof. induction l as [|a l IH]; intros f g; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma sumf_scal : forall l c f, sumf l (fun k => c * f k) = c * sumf l f.
Proof. induction l as [|a l IH]; intros c f; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma sumf_swap : forall l1 l2 F,
  sumf l1 (fun i => sumf l2 (fun j => F i j))
  = sumf l2 (fun j => sumf l1 (fun i => F i j)).
Proof.
  induction l1 as [|a l1 IH]; intros l2 F; simpl.
  - symmetry; apply sumf_zero.
  - rewrite IH, <- sumf_add; reflexivity.
Qed.

Lemma sumf_sift : forall l m g, NoDup l -> In m l ->
  sumf l (fun k => if (m =? k)%nat then g k else 0%Z) = g m.
Proof.
  induction l as [|a l IH]; intros m g Hnd Hin; [ inversion Hin | ].
  simpl; inversion Hnd as [|x xs Hna Hnd' Heq]; subst.
  destruct (Nat.eqb_spec m a) as [->|Hne].
  - rewrite (sumf_ext l (fun k => if (a =? k)%nat then g k else 0%Z) (fun _ => 0%Z)).
    + rewrite sumf_zero; ring.
    + intros k Hk; destruct (Nat.eqb_spec a k) as [->|_];
        [ exfalso; apply Hna; exact Hk | reflexivity ].
  - destruct Hin as [->|Hin]; [ exfalso; apply Hne; reflexivity | ].
    rewrite IH by assumption; ring.
Qed.

Lemma bigsum_mul_r : forall f c, bigsum f * c = bigsum (fun k => f k * c).
Proof.
  intros f c; unfold bigsum; rewrite Z.mul_comm, <- sumf_scal.
  apply sumf_ext; intros; ring.
Qed.

Lemma bigsum_swap : forall F,
  bigsum (fun i => bigsum (fun j => F i j)) = bigsum (fun j => bigsum (fun i => F i j)).
Proof. intros; unfold bigsum; apply sumf_swap. Qed.

(* ================================================================= *)
(*  Double sums over the group, and the swap we need                 *)
(* ================================================================= *)
Definition dsum (F : nat -> nat -> Z) : Z := bigsum (fun i => bigsum (fun j => F i j)).

Lemma dsum_mul_r : forall F c, dsum F * c = dsum (fun i j => F i j * c).
Proof.
  intros F c; unfold dsum; rewrite bigsum_mul_r.
  apply sumf_ext; intros i _; apply bigsum_mul_r.
Qed.

Lemma bigsum_dsum_swap : forall F,
  bigsum (fun k => dsum (fun i j => F k i j)) = dsum (fun i j => bigsum (fun k => F k i j)).
Proof.
  intros F; unfold dsum.
  rewrite bigsum_swap.
  apply sumf_ext; intros i _; apply bigsum_swap.
Qed.

(* ================================================================= *)
(*  The group algebra structure                                       *)
(* ================================================================= *)
Definition gunit : nat -> Z := fun k => if (k =? 0)%nat then 1 else 0.
Definition gconv (a b : nat -> Z) : nat -> Z :=
  fun k => dsum (fun i j => if ((i + j) mod n =? k)%nat then a i * b j else 0).
Definition ginv (a : nat -> Z) : nat -> Z := fun k => a ((n - k) mod n)%nat.

(* the pairing ⟨a, φ⟩ = Σ_g a_g φ_g *)
Definition dot (a phi : nat -> Z) : Z := bigsum (fun k => a k * phi k).

(* ================================================================= *)
(*  DUALITY 1 (product ↔ coproduct):                                 *)
(*     ⟨a ⋆ b, φ⟩ = Σ_{i,j} a_i b_j φ_{(i+j) mod n}                   *)
(*  convolution in k[G] is dual to the coproduct (Δφ)(i,j)=φ_{i+j}    *)
(*  of the function algebra k^G.                                      *)
(* ================================================================= *)
Theorem product_coproduct_duality : forall a b phi,
  dot (gconv a b) phi = dsum (fun i j => a i * b j * phi ((i + j) mod n)%nat).
Proof.
  intros a b phi; unfold dot.
  transitivity
    (bigsum (fun k => dsum (fun i j =>
       (if ((i + j) mod n =? k)%nat then a i * b j else 0) * phi k))).
  { apply sumf_ext; intros k _; unfold gconv; rewrite dsum_mul_r; reflexivity. }
  rewrite bigsum_dsum_swap.
  apply sumf_ext; intros i _; apply sumf_ext; intros j _.
  transitivity (bigsum (fun k =>
      if ((i + j) mod n =? k)%nat then (a i * b j * phi k) else 0)).
  { apply sumf_ext; intros k _; destruct ((i + j) mod n =? k)%nat; ring. }
  assert (Hm : ((i + j) mod n < n)%nat) by (apply Nat.mod_upper_bound; lia).
  unfold bigsum; rewrite (sumf_sift (seq 0 n) ((i + j) mod n)%nat (fun k => a i * b j * phi k)).
  - reflexivity.
  - apply seq_NoDup.
  - apply in_seq; lia.
Qed.

(* ================================================================= *)
(*  DUALITY 2 (coproduct ↔ product):                                 *)
(*     ⟨a, φ·ψ⟩ = Σ_g a_g φ_g ψ_g                                    *)
(*  the (diagonal) coproduct of k[G] is dual to the pointwise         *)
(*  product of k^G.                                                   *)
(* ================================================================= *)
Theorem coproduct_product_duality : forall a phi psi,
  dot a (fun k => phi k * psi k) = bigsum (fun g => a g * phi g * psi g).
Proof. intros; unfold dot; apply sumf_ext; intros; ring. Qed.

(* ================================================================= *)
(*  COUNIT / UNIT duality                                             *)
(*     ⟨e_0, φ⟩ = φ_0        (unit of k[G] ↔ counit of k^G)          *)
(*     ⟨a, 1⟩  = Σ_g a_g     (counit of k[G] ↔ unit of k^G)          *)
(* ================================================================= *)
Theorem counit_unit_pairing : forall phi, dot gunit phi = phi 0%nat.
Proof.
  intros phi; unfold dot, gunit.
  transitivity (bigsum (fun k => if (0 =? k)%nat then phi k else 0)).
  { apply sumf_ext; intros k _; rewrite (Nat.eqb_sym k 0); destruct (0 =? k)%nat; ring. }
  unfold bigsum; rewrite (sumf_sift (seq 0 n) 0%nat phi).
  - reflexivity.
  - apply seq_NoDup.
  - apply in_seq; lia.
Qed.

Theorem counit_augmentation : forall a, dot a (fun _ => 1) = bigsum a.
Proof. intros a; unfold dot; apply sumf_ext; intros; ring. Qed.

(* ================================================================= *)
(*  THE ANTIPODE AXIOM:  m∘(S⊗id)∘Δ = η∘ε                            *)
(*  Δ is diagonal, so (S⊗id)Δ(a) = Σ_g a_g e_{−g}⊗e_g and m collapses *)
(*  it to Σ_g a_g e_{(−g)+g} = (Σ_g a_g) e_0 = ε(a)·1.               *)
(* ================================================================= *)
Definition SidDelta (a : nat -> Z) : nat -> Z :=
  fun k => bigsum (fun g => if ((((n - g) mod n) + g) mod n =? k)%nat then a g else 0).

Lemma neg_add_zero : forall g, (g < n)%nat -> ((((n - g) mod n) + g) mod n = 0)%nat.
Proof.
  intros g Hg; rewrite Nat.Div0.add_mod_idemp_l.
  replace (n - g + g)%nat with n by lia.
  apply Nat.Div0.mod_same.
Qed.

Theorem antipode_axiom : forall a k,
  SidDelta a k = (if (k =? 0)%nat then bigsum a else 0).
Proof.
  intros a k; unfold SidDelta.
  transitivity (bigsum (fun g => if (0 =? k)%nat then a g else 0)).
  { apply sumf_ext; intros g Hg; apply in_seq in Hg.
    rewrite neg_add_zero by lia; reflexivity. }
  rewrite (Nat.eqb_sym 0 k); destruct (k =? 0)%nat.
  - apply sumf_ext; intros; reflexivity.
  - transitivity (bigsum (fun _ : nat => 0%Z)).
    + apply sumf_ext; intros; reflexivity.
    + unfold bigsum; apply sumf_zero.
Qed.

(* The right-hand side is exactly ε(a)·e_0 = (bigsum a)·gunit. *)
Corollary antipode_is_eps_unit : forall a k,
  SidDelta a k = gunit k * bigsum a.
Proof.
  intros a k; rewrite antipode_axiom; unfold gunit; destruct (k =? 0)%nat; ring.
Qed.

End GroupAlgebra.

Print Assumptions product_coproduct_duality.
Print Assumptions coproduct_product_duality.
Print Assumptions antipode_axiom.

(* ================================================================= *)
(*  END HopfGroupAlgebra.v                                            *)
(*  k[ℤ/nℤ] as a Hopf algebra (convolution product, diagonal          *)
(*  coproduct, augmentation counit, inversion antipode) in duality    *)
(*  with the function algebra k^{ℤ/nℤ}: convolution ↔ coproduct,       *)
(*  diagonal coproduct ↔ pointwise product, unit ↔ counit, and the    *)
(*  antipode axiom m∘(S⊗id)∘Δ = η∘ε.  Combinatorial, no roots of      *)
(*  unity.  Closed under the global context (axiom-free).             *)
(* ================================================================= *)
