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
  simpl; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (Nat.eqb_spec m a) as [->|Hne].
  - rewrite (sumf_ext l (fun k => if (a =? k)%nat then g k else 0%Z) (fun _ => 0%Z)).
    + rewrite sumf_zero; ring.
    + intros k Hk; destruct (Nat.eqb_spec a k) as [->|_];
        [ exfalso; apply Hna; exact Hk | reflexivity ].
  - destruct Hin as [->|Hin]; [ exfalso; apply Hne; reflexivity | ].
    rewrite IH by assumption; ring.
Qed.

Lemma sumf_single : forall l m h, NoDup l -> In m l ->
  (forall j, In j l -> j <> m -> h j = 0%Z) -> sumf l h = h m.
Proof.
  induction l as [|a l IH]; intros m h Hnd Hin Hz; [ inversion Hin | ].
  simpl; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (Nat.eq_dec a m) as [->|Hne].
  - rewrite (sumf_ext l h (fun _ => 0%Z)).
    + rewrite sumf_zero; ring.
    + intros j Hj; apply Hz; [ right; exact Hj | intro Heq; subst; contradiction ].
  - destruct Hin as [->|Hin]; [ contradiction | ].
    rewrite (Hz a (or_introl eq_refl) Hne), (IH m h Hnd' Hin); [ ring | ].
    intros j Hj Hjm; apply Hz; [ right; exact Hj | exact Hjm ].
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

(* ================================================================= *)
(*  CONVOLUTION RING AXIOMS  and  S² = id                            *)
(*  Equalities of elements are stated pointwise on representatives    *)
(*  (k < n) — the honest notion of equality in k[ℤ/nℤ].              *)
(* ================================================================= *)

(* coefficient extraction: pair against a delta function *)
Definition delta (k : nat) : nat -> Z := fun j => if (k =? j)%nat then 1 else 0.

Lemma dot_delta : forall x k, (k < n)%nat -> dot x (delta k) = x k.
Proof.
  intros x k Hk; unfold dot, delta.
  transitivity (bigsum (fun j => if (k =? j)%nat then x j else 0)).
  { apply sumf_ext; intros j _; destruct (k =? j)%nat; ring. }
  unfold bigsum; rewrite (sumf_sift (seq 0 n) k x);
    [ reflexivity | apply seq_NoDup | apply in_seq; lia ].
Qed.

Lemma dsum_swap : forall F, dsum F = dsum (fun i j => F j i).
Proof. intros F; unfold dsum; apply bigsum_swap. Qed.

(* COMMUTATIVITY:  a ⋆ b = b ⋆ a  *)
Theorem gconv_comm : forall a b k, gconv a b k = gconv b a k.
Proof.
  intros a b k; unfold gconv.
  rewrite (dsum_swap (fun i j => if ((i + j) mod n =? k)%nat then a i * b j else 0)).
  apply sumf_ext; intros i _; apply sumf_ext; intros j _.
  rewrite (Nat.add_comm j i); destruct ((i + j) mod n =? k)%nat; ring.
Qed.

(* DISTRIBUTIVITY over addition (both sides) *)
Theorem gconv_distrib_l : forall a b c k,
  gconv a (fun j => b j + c j) k = gconv a b k + gconv a c k.
Proof.
  intros a b c k; unfold gconv, dsum, bigsum.
  rewrite <- sumf_add; apply sumf_ext; intros i _.
  rewrite <- sumf_add; apply sumf_ext; intros j _.
  destruct ((i + j) mod n =? k)%nat; ring.
Qed.

Theorem gconv_distrib_r : forall a b c k,
  gconv (fun i => a i + b i) c k = gconv a c k + gconv b c k.
Proof.
  intros a b c k; unfold gconv, dsum, bigsum.
  rewrite <- sumf_add; apply sumf_ext; intros i _.
  rewrite <- sumf_add; apply sumf_ext; intros j _.
  destruct ((i + j) mod n =? k)%nat; ring.
Qed.

(* UNIT:  e_0 ⋆ a = a = a ⋆ e_0   (on representatives) *)
Theorem gconv_unit_r : forall a k, (k < n)%nat -> gconv a gunit k = a k.
Proof.
  intros a k Hk; unfold gconv, gunit, dsum, bigsum.
  transitivity (sumf (seq 0 n) (fun i => if (i mod n =? k)%nat then a i else 0)).
  { apply sumf_ext; intros i _.
    rewrite (sumf_single (seq 0 n) 0%nat
      (fun j => if ((i + j) mod n =? k)%nat then a i * (if (j =? 0)%nat then 1 else 0) else 0)).
    - cbn beta; rewrite Nat.add_0_r.
      change (if (0 =? 0)%nat then 1%Z else 0%Z) with 1%Z.
      destruct (i mod n =? k)%nat; ring.
    - apply seq_NoDup.
    - apply in_seq; lia.
    - intros j _ Hj0; destruct (j =? 0)%nat eqn:Ej.
      + apply Nat.eqb_eq in Ej; contradiction.
      + change (if false then 1%Z else 0%Z) with 0%Z.
        destruct ((i + j) mod n =? k)%nat; ring. }
  transitivity (sumf (seq 0 n) (fun i => if (k =? i)%nat then a i else 0)).
  { apply sumf_ext; intros i Hi; apply in_seq in Hi.
    rewrite Nat.mod_small by lia; rewrite (Nat.eqb_sym i k); reflexivity. }
  rewrite (sumf_sift (seq 0 n) k a); [ reflexivity | apply seq_NoDup | apply in_seq; lia ].
Qed.

Theorem gconv_unit_l : forall a k, (k < n)%nat -> gconv gunit a k = a k.
Proof. intros a k Hk; rewrite gconv_comm; apply gconv_unit_r; exact Hk. Qed.

(* ASSOCIATIVITY, via the duality:  ⟨(a⋆b)⋆c, φ⟩ = ⟨a⋆(b⋆c), φ⟩,      *)
(* both equal Σ_{i,j,m} a_i b_j c_m φ_{i+j+m}; extract coefficients.   *)
Lemma dot_R : forall a b c phi,
  dot (gconv a (gconv b c)) phi
  = bigsum (fun i => bigsum (fun j => bigsum (fun m =>
      a i * b j * c m * phi ((i + j + m) mod n)%nat))).
Proof.
  intros a b c phi.
  rewrite (product_coproduct_duality a (gconv b c) phi); unfold dsum.
  apply sumf_ext; intros i _.
  transitivity (dot (gconv b c) (fun q => a i * phi ((i + q) mod n)%nat)).
  { unfold dot; apply sumf_ext; intros q _; ring. }
  rewrite (product_coproduct_duality b c (fun q => a i * phi ((i + q) mod n)%nat)); unfold dsum.
  apply sumf_ext; intros j _; apply sumf_ext; intros m _; cbn beta.
  rewrite Nat.Div0.add_mod_idemp_r.
  replace (i + (j + m))%nat with (i + j + m)%nat by lia; ring.
Qed.

Lemma dot_L : forall a b c phi,
  dot (gconv (gconv a b) c) phi
  = bigsum (fun i => bigsum (fun j => bigsum (fun m =>
      a i * b j * c m * phi ((i + j + m) mod n)%nat))).
Proof.
  intros a b c phi.
  rewrite (product_coproduct_duality (gconv a b) c phi); unfold dsum.
  rewrite bigsum_swap.
  transitivity (bigsum (fun m => bigsum (fun i => bigsum (fun j =>
      a i * b j * c m * phi ((i + j + m) mod n)%nat)))).
  { apply sumf_ext; intros m _.
    transitivity (dot (gconv a b) (fun p => c m * phi ((p + m) mod n)%nat)).
    { unfold dot; apply sumf_ext; intros p _; ring. }
    rewrite (product_coproduct_duality a b (fun p => c m * phi ((p + m) mod n)%nat)); unfold dsum.
    apply sumf_ext; intros i _; apply sumf_ext; intros j _; cbn beta.
    rewrite Nat.Div0.add_mod_idemp_l; ring. }
  rewrite bigsum_swap; apply sumf_ext; intros i _; apply bigsum_swap.
Qed.

Theorem gconv_assoc : forall a b c k, (k < n)%nat ->
  gconv (gconv a b) c k = gconv a (gconv b c) k.
Proof.
  intros a b c k Hk.
  rewrite <- (dot_delta (gconv (gconv a b) c) k Hk).
  rewrite <- (dot_delta (gconv a (gconv b c)) k Hk).
  rewrite dot_L, dot_R; reflexivity.
Qed.

(* ANTIPODE INVOLUTIVITY:  S² = id   (on representatives) *)
Theorem ginv_involutive : forall a k, (k < n)%nat -> ginv (ginv a) k = a k.
Proof.
  intros a k Hk; unfold ginv.
  assert (Hkm : ((n - (n - k) mod n) mod n = k)%nat).
  { destruct (Nat.eq_dec k 0) as [->|Hk0].
    - rewrite Nat.sub_0_r, Nat.Div0.mod_same, Nat.sub_0_r, Nat.Div0.mod_same; reflexivity.
    - rewrite (Nat.mod_small (n - k)) by lia.
      replace (n - (n - k))%nat with k by lia.
      apply Nat.mod_small; lia. }
  rewrite Hkm; reflexivity.
Qed.

End GroupAlgebra.

Print Assumptions product_coproduct_duality.
Print Assumptions coproduct_product_duality.
Print Assumptions antipode_axiom.
Print Assumptions gconv_assoc.
Print Assumptions gconv_comm.
Print Assumptions gconv_unit_r.
Print Assumptions ginv_involutive.

(* ================================================================= *)
(*  END HopfGroupAlgebra.v                                            *)
(*  k[ℤ/nℤ] as a Hopf algebra (convolution product, diagonal          *)
(*  coproduct, augmentation counit, inversion antipode) in duality    *)
(*  with the function algebra k^{ℤ/nℤ}: convolution ↔ coproduct,       *)
(*  diagonal coproduct ↔ pointwise product, unit ↔ counit, and the    *)
(*  antipode axiom m∘(S⊗id)∘Δ = η∘ε.  Combinatorial, no roots of      *)
(*  unity.  Closed under the global context (axiom-free).             *)
(* ================================================================= *)
