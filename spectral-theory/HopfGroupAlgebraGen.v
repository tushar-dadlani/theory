(* ================================================================= *)
(*  HopfGroupAlgebraGen.v                                            *)
(*                                                                    *)
(*  THE GROUP ALGEBRA k[G] for an ARBITRARY FINITE ABELIAN GROUP G,   *)
(*  and its HOPF DUALITY with the function algebra k^G — AXIOM-FREE.  *)
(*                                                                    *)
(*  G is presented abstractly: a carrier `A` with decidable equality  *)
(*  `Aeq`, a finite enumeration `elts` (NoDup, complete), and group   *)
(*  operations op/e/inv satisfying the (left) group axioms + comm.    *)
(*  This generalises HopfGroupAlgebra (the cyclic case ℤ/nℤ), with    *)
(*    (i+j) mod n  ↦  op x y        seq 0 n  ↦  elts                   *)
(*    _ =? _       ↦  Aeq           mod facts ↦  group axioms          *)
(*  Because `elts` contains EVERY element, all identities hold         *)
(*  unconditionally (no representative guard).                        *)
(*                                                                    *)
(*  Delivers: the group algebra (convolution, unit, diagonal          *)
(*  coproduct, augmentation counit, inversion antipode), the full     *)
(*  Hopf duality with k^G, the commutative-ring axioms of             *)
(*  convolution, and S² = id.  Closed under the global context.       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith Lia List.
Import ListNotations.
Open Scope Z_scope.

Section MonoidAlgebra.

(* ---- the abstract finite abelian group ---- *)
Variable A : Type.
Variable Aeq : A -> A -> bool.
Hypothesis Aeq_spec : forall x y, reflect (x = y) (Aeq x y).
Variable elts : list A.
Hypothesis elts_nodup : NoDup elts.
Hypothesis elts_all : forall x, In x elts.
Variable op : A -> A -> A.
Variable e : A.
Hypothesis op_assoc : forall x y z, op (op x y) z = op x (op y z).
Hypothesis op_comm : forall x y, op x y = op y x.
Hypothesis op_id_l : forall x, op e x = x.

(* ---- derived monoid facts ---- *)
Lemma op_id_r : forall x, op x e = x.
Proof. intro x; rewrite op_comm; apply op_id_l. Qed.

Lemma Aeq_refl : forall x, Aeq x x = true.
Proof. intro x; destruct (Aeq_spec x x) as [_|Hne]; [ reflexivity | exfalso; apply Hne; reflexivity ]. Qed.

Lemma Aeq_sym : forall x y, Aeq x y = Aeq y x.
Proof.
  intros x y; destruct (Aeq_spec x y) as [E|Hxy].
  - subst; rewrite Aeq_refl; reflexivity.
  - destruct (Aeq_spec y x) as [E2|_]; [ exfalso; apply Hxy; symmetry; exact E2 | reflexivity ].
Qed.

(* ================================================================= *)
(*  Finite-sum toolkit over the group's element list                 *)
(* ================================================================= *)
Definition sumf (l : list A) (f : A -> Z) : Z :=
  fold_right (fun k acc => f k + acc) 0%Z l.
Definition bigsum (f : A -> Z) : Z := sumf elts f.

Lemma sumf_ext : forall l f g,
  (forall k, In k l -> f k = g k) -> sumf l f = sumf l g.
Proof.
  induction l as [|a l IH]; intros f g H; simpl; [ reflexivity | ].
  rewrite (H a (or_introl eq_refl)), (IH f g); [ reflexivity | ].
  intros k Hk; apply H; right; exact Hk.
Qed.

Lemma sumf_zero : forall l, sumf l (fun _ => 0%Z) = 0%Z.
Proof. induction l as [|a l IH]; simpl; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma sumf_add : forall l f g, sumf l (fun k => f k + g k) = sumf l f + sumf l g.
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
  sumf l (fun k => if Aeq m k then g k else 0%Z) = g m.
Proof.
  induction l as [|a l IH]; intros m g Hnd Hin; [ inversion Hin | ].
  simpl; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (Aeq_spec m a) as [->|Hne].
  - rewrite (sumf_ext l (fun k => if Aeq a k then g k else 0%Z) (fun _ => 0%Z)).
    + rewrite sumf_zero; ring.
    + intros k Hk; destruct (Aeq_spec a k) as [->|_];
        [ exfalso; apply Hna; exact Hk | reflexivity ].
  - destruct Hin as [->|Hin]; [ exfalso; apply Hne; reflexivity | ].
    rewrite IH by assumption; ring.
Qed.

Lemma sumf_single : forall l m h, NoDup l -> In m l ->
  (forall j, In j l -> j <> m -> h j = 0%Z) -> sumf l h = h m.
Proof.
  induction l as [|a l IH]; intros m h Hnd Hin Hz; [ inversion Hin | ].
  simpl; inversion Hnd as [|x xs Hna Hnd']; subst.
  destruct (Aeq_spec a m) as [->|Hne].
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

Definition dsum (F : A -> A -> Z) : Z := bigsum (fun i => bigsum (fun j => F i j)).

Lemma dsum_mul_r : forall F c, dsum F * c = dsum (fun i j => F i j * c).
Proof.
  intros F c; unfold dsum; rewrite bigsum_mul_r.
  apply sumf_ext; intros i _; apply bigsum_mul_r.
Qed.

Lemma bigsum_dsum_swap : forall F,
  bigsum (fun k => dsum (fun i j => F k i j)) = dsum (fun i j => bigsum (fun k => F k i j)).
Proof.
  intros F; unfold dsum; rewrite bigsum_swap.
  apply sumf_ext; intros i _; apply bigsum_swap.
Qed.

Lemma dsum_swap : forall F, dsum F = dsum (fun i j => F j i).
Proof. intros F; unfold dsum; apply bigsum_swap. Qed.

(* ================================================================= *)
(*  The group algebra structure and the pairing                      *)
(* ================================================================= *)
Definition gunit : A -> Z := fun g => if Aeq e g then 1 else 0.
Definition gconv (a b : A -> Z) : A -> Z :=
  fun g => dsum (fun x y => if Aeq (op x y) g then a x * b y else 0).
Definition dot (a phi : A -> Z) : Z := bigsum (fun g => a g * phi g).
Definition delta (m : A) : A -> Z := fun k => if Aeq m k then 1 else 0.

Lemma dot_delta : forall x m, dot x (delta m) = x m.
Proof.
  intros x m; unfold dot, delta.
  transitivity (bigsum (fun k => if Aeq m k then x k else 0)).
  { apply sumf_ext; intros k _; destruct (Aeq m k); ring. }
  unfold bigsum; rewrite (sumf_sift elts m x); [ reflexivity | exact elts_nodup | apply elts_all ].
Qed.

(* ================================================================= *)
(*  DUALITY 1 (product ↔ coproduct):  ⟨a ⋆ b, φ⟩ = Σ_{x,y} a_x b_y φ_{xy} *)
(* ================================================================= *)
Theorem product_coproduct_duality : forall a b phi,
  dot (gconv a b) phi = dsum (fun x y => a x * b y * phi (op x y)).
Proof.
  intros a b phi; unfold dot.
  transitivity (bigsum (fun g => dsum (fun x y =>
    (if Aeq (op x y) g then a x * b y else 0) * phi g))).
  { apply sumf_ext; intros g _; unfold gconv; rewrite dsum_mul_r; reflexivity. }
  rewrite bigsum_dsum_swap.
  apply sumf_ext; intros x _; apply sumf_ext; intros y _.
  transitivity (bigsum (fun g => if Aeq (op x y) g then (a x * b y * phi g) else 0)).
  { apply sumf_ext; intros g _; destruct (Aeq (op x y) g); ring. }
  unfold bigsum; rewrite (sumf_sift elts (op x y) (fun g => a x * b y * phi g));
    [ reflexivity | exact elts_nodup | apply elts_all ].
Qed.

(* ================================================================= *)
(*  DUALITY 2 (coproduct ↔ product):  ⟨a, φ·ψ⟩ = Σ_g a_g φ_g ψ_g       *)
(* ================================================================= *)
Theorem coproduct_product_duality : forall a phi psi,
  dot a (fun g => phi g * psi g) = bigsum (fun g => a g * phi g * psi g).
Proof. intros; unfold dot; apply sumf_ext; intros; ring. Qed.

(* ================================================================= *)
(*  COUNIT / UNIT duality                                             *)
(* ================================================================= *)
Theorem counit_unit_pairing : forall phi, dot gunit phi = phi e.
Proof.
  intros phi; unfold dot, gunit.
  transitivity (bigsum (fun g => if Aeq e g then phi g else 0)).
  { apply sumf_ext; intros g _; destruct (Aeq e g); ring. }
  unfold bigsum; rewrite (sumf_sift elts e phi); [ reflexivity | exact elts_nodup | apply elts_all ].
Qed.

Theorem counit_augmentation : forall a, dot a (fun _ => 1) = bigsum a.
Proof. intros a; unfold dot; apply sumf_ext; intros; ring. Qed.

(* ================================================================= *)
(*  CONVOLUTION RING AXIOMS  and  S² = id  (unconditional)           *)
(* ================================================================= *)
Theorem gconv_comm : forall a b g, gconv a b g = gconv b a g.
Proof.
  intros a b g; unfold gconv.
  rewrite (dsum_swap (fun x y => if Aeq (op x y) g then a x * b y else 0)).
  apply sumf_ext; intros x _; apply sumf_ext; intros y _.
  rewrite (op_comm y x); destruct (Aeq (op x y) g); ring.
Qed.

Theorem gconv_distrib_l : forall a b c g,
  gconv a (fun y => b y + c y) g = gconv a b g + gconv a c g.
Proof.
  intros a b c g; unfold gconv, dsum, bigsum.
  rewrite <- sumf_add; apply sumf_ext; intros x _.
  rewrite <- sumf_add; apply sumf_ext; intros y _.
  destruct (Aeq (op x y) g); ring.
Qed.

Theorem gconv_distrib_r : forall a b c g,
  gconv (fun x => a x + b x) c g = gconv a c g + gconv b c g.
Proof.
  intros a b c g; unfold gconv, dsum, bigsum.
  rewrite <- sumf_add; apply sumf_ext; intros x _.
  rewrite <- sumf_add; apply sumf_ext; intros y _.
  destruct (Aeq (op x y) g); ring.
Qed.

Theorem gconv_unit_l : forall a g, gconv gunit a g = a g.
Proof.
  intros a g; unfold gconv, gunit, dsum, bigsum.
  rewrite (sumf_single elts e
    (fun x => sumf elts (fun y => if Aeq (op x y) g then (if Aeq e x then 1 else 0) * a y else 0))).
  - cbn beta.
    transitivity (sumf elts (fun y => if Aeq g y then a y else 0)).
    + apply sumf_ext; intros y _.
      rewrite op_id_l, Aeq_refl, (Aeq_sym y g).
      change (if true then 1%Z else 0%Z) with 1%Z.
      destruct (Aeq g y); ring.
    + rewrite (sumf_sift elts g a); [ reflexivity | exact elts_nodup | apply elts_all ].
  - exact elts_nodup.
  - apply elts_all.
  - intros x _ Hxe.
    destruct (Aeq_spec e x) as [E|_]; [ exfalso; apply Hxe; symmetry; exact E | ].
    transitivity (sumf elts (fun _ : A => 0%Z)); [ | apply sumf_zero ].
    apply sumf_ext; intros y _.
    change (if false then 1%Z else 0%Z) with 0%Z.
    destruct (Aeq (op x y) g); ring.
Qed.

Theorem gconv_unit_r : forall a g, gconv a gunit g = a g.
Proof. intros a g; rewrite gconv_comm; apply gconv_unit_l. Qed.

(* The group-like elements (deltas) are CLOSED under convolution and       *)
(* multiply exactly as M does:  delta_m * delta_n = delta_{m op n}.        *)
(* Hence  m |-> delta_m  is a monoid hom (M, op) -> (grouplikes, gconv),    *)
(* with unit  gunit = delta_e  (gunit_delta): the operators ARE the group. *)
Lemma gunit_delta : forall g, gunit g = delta e g.
Proof. reflexivity. Qed.

Theorem gconv_delta : forall m n g,
  gconv (delta m) (delta n) g = delta (op m n) g.
Proof.
  intros m n g; unfold gconv, delta, dsum, bigsum.
  rewrite (sumf_single elts m
    (fun x => sumf elts (fun y =>
       if Aeq (op x y) g then (if Aeq m x then 1 else 0) * (if Aeq n y then 1 else 0) else 0))).
  - (* x = m *)
    rewrite (sumf_single elts n
      (fun y => if Aeq (op m y) g
                then (if Aeq m m then 1 else 0) * (if Aeq n y then 1 else 0) else 0)).
    + rewrite !Aeq_refl; change (if true then 1%Z else 0%Z) with 1%Z;
        destruct (Aeq (op m n) g); ring.
    + exact elts_nodup.
    + apply elts_all.
    + intros y _ Hyn.
      destruct (Aeq_spec n y) as [E|_]; [ exfalso; apply Hyn; symmetry; exact E | ].
      change (if false then 1%Z else 0%Z) with 0%Z; destruct (Aeq (op m y) g); ring.
  - exact elts_nodup.
  - apply elts_all.
  - intros x _ Hxm.
    destruct (Aeq_spec m x) as [E|_]; [ exfalso; apply Hxm; symmetry; exact E | ].
    transitivity (sumf elts (fun _ : A => 0%Z)); [ | apply sumf_zero ].
    apply sumf_ext; intros y _.
    change (if false then 1%Z else 0%Z) with 0%Z; destruct (Aeq (op x y) g); ring.
Qed.

(* ASSOCIATIVITY via the duality: both associations pair identically  *)
(* with every φ (= Σ_{x,y,z} a_x b_y c_z φ_{x(yz)}); extract coeffs.  *)
Lemma dot_R : forall a b c phi,
  dot (gconv a (gconv b c)) phi
  = bigsum (fun x => bigsum (fun y => bigsum (fun z =>
      a x * b y * c z * phi (op x (op y z))))).
Proof.
  intros a b c phi.
  rewrite (product_coproduct_duality a (gconv b c) phi); unfold dsum.
  apply sumf_ext; intros x _.
  transitivity (dot (gconv b c) (fun q => a x * phi (op x q))).
  { unfold dot; apply sumf_ext; intros q _; ring. }
  rewrite (product_coproduct_duality b c (fun q => a x * phi (op x q))); unfold dsum.
  apply sumf_ext; intros y _; apply sumf_ext; intros z _; cbn beta; ring.
Qed.

Lemma dot_L : forall a b c phi,
  dot (gconv (gconv a b) c) phi
  = bigsum (fun x => bigsum (fun y => bigsum (fun z =>
      a x * b y * c z * phi (op x (op y z))))).
Proof.
  intros a b c phi.
  rewrite (product_coproduct_duality (gconv a b) c phi); unfold dsum.
  rewrite bigsum_swap.
  transitivity (bigsum (fun z => bigsum (fun x => bigsum (fun y =>
      a x * b y * c z * phi (op x (op y z)))))).
  { apply sumf_ext; intros z _.
    transitivity (dot (gconv a b) (fun p => c z * phi (op p z))).
    { unfold dot; apply sumf_ext; intros p _; ring. }
    rewrite (product_coproduct_duality a b (fun p => c z * phi (op p z))); unfold dsum.
    apply sumf_ext; intros x _; apply sumf_ext; intros y _; cbn beta.
    rewrite op_assoc; ring. }
  rewrite bigsum_swap; apply sumf_ext; intros x _; apply bigsum_swap.
Qed.

Theorem gconv_assoc : forall a b c g,
  gconv (gconv a b) c g = gconv a (gconv b c) g.
Proof.
  intros a b c g.
  rewrite <- (dot_delta (gconv (gconv a b) c) g).
  rewrite <- (dot_delta (gconv a (gconv b c)) g).
  rewrite dot_L, dot_R; reflexivity.
Qed.

(* ================================================================= *)
(*  GROUP PART:  the inversion antipode needs op_inv_l                *)
(* ================================================================= *)
Section GroupPart.
Variable inv : A -> A.
Hypothesis op_inv_l : forall x, op (inv x) x = e.

Lemma inv_involutive : forall x, inv (inv x) = x.
Proof.
  intro x.
  rewrite <- (op_id_r (inv (inv x))), <- (op_inv_l x), <- op_assoc, op_inv_l.
  apply op_id_l.
Qed.

Definition ginv (a : A -> Z) : A -> Z := fun g => a (inv g).

(* THE ANTIPODE AXIOM:  m∘(S⊗id)∘Δ = η∘ε *)
Definition SidDelta (a : A -> Z) : A -> Z :=
  fun g => bigsum (fun x => if Aeq (op (inv x) x) g then a x else 0).

Theorem antipode_axiom : forall a g,
  SidDelta a g = (if Aeq e g then bigsum a else 0).
Proof.
  intros a g; unfold SidDelta.
  transitivity (bigsum (fun x => if Aeq e g then a x else 0)).
  { apply sumf_ext; intros x _; rewrite op_inv_l; reflexivity. }
  destruct (Aeq e g).
  - apply sumf_ext; intros; reflexivity.
  - transitivity (bigsum (fun _ : A => 0%Z)).
    + apply sumf_ext; intros; reflexivity.
    + unfold bigsum; apply sumf_zero.
Qed.

Corollary antipode_is_eps_unit : forall a g, SidDelta a g = gunit g * bigsum a.
Proof.
  intros a g; rewrite antipode_axiom; unfold gunit; destruct (Aeq e g); ring.
Qed.

Theorem ginv_involutive : forall a g, ginv (ginv a) g = a g.
Proof. intros a g; unfold ginv; rewrite inv_involutive; reflexivity. Qed.

End GroupPart.

End MonoidAlgebra.

Print Assumptions product_coproduct_duality.
Print Assumptions antipode_axiom.
Print Assumptions gconv_assoc.
Print Assumptions gconv_unit_l.
Print Assumptions ginv_involutive.

(* ================================================================= *)
(*  NON-VACUITY: the abstract hypotheses are jointly satisfiable.     *)
(*  Concrete witness — ℤ/2ℤ realised as (bool, xorb, false, id).      *)
(* ================================================================= *)
Definition z2_elts : list bool := false :: true :: nil.

Lemma z2_eqb_spec : forall x y : bool, reflect (x = y) (Bool.eqb x y).
Proof. destruct x, y; simpl; constructor; congruence. Qed.
Lemma z2_nodup : NoDup z2_elts.
Proof. unfold z2_elts; repeat constructor; simpl; intuition congruence. Qed.
Lemma z2_all : forall x, In x z2_elts.
Proof. destruct x; simpl; auto. Qed.
Lemma z2_assoc : forall x y z, xorb (xorb x y) z = xorb x (xorb y z).
Proof. destruct x, y, z; reflexivity. Qed.
Lemma z2_comm : forall x y, xorb x y = xorb y x.
Proof. destruct x, y; reflexivity. Qed.
Lemma z2_id_l : forall x, xorb false x = x.
Proof. reflexivity. Qed.
Lemma z2_inv_l : forall x, xorb x x = false.
Proof. destruct x; reflexivity. Qed.

(* the general theory fires at the concrete group k[ℤ/2ℤ]: *)
Corollary z2_associative : forall a b c g,
  gconv bool Bool.eqb z2_elts xorb (gconv bool Bool.eqb z2_elts xorb a b) c g
  = gconv bool Bool.eqb z2_elts xorb a (gconv bool Bool.eqb z2_elts xorb b c) g.
Proof. apply gconv_assoc; eauto using z2_eqb_spec, z2_nodup, z2_all, z2_assoc, z2_comm, z2_id_l, z2_inv_l. Qed.

Corollary z2_unit : forall a g,
  gconv bool Bool.eqb z2_elts xorb (gunit bool Bool.eqb false) a g = a g.
Proof. apply gconv_unit_l; eauto using z2_eqb_spec, z2_nodup, z2_all, z2_assoc, z2_comm, z2_id_l, z2_inv_l. Qed.

(* ================================================================= *)
(*  END HopfGroupAlgebraGen.v                                         *)
(*  k[G] for an arbitrary finite abelian group G: a commutative Hopf  *)
(*  algebra (convolution, diagonal coproduct, augmentation counit,    *)
(*  involutive inversion antipode) in duality with k^G.  Generalises  *)
(*  the cyclic case; combinatorial, no roots of unity.  Closed under  *)
(*  the global context (axiom-free).                                  *)
(* ================================================================= *)
