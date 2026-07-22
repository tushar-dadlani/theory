(* ================================================================= *)
(*  BiViewProduct.v                                                   *)
(*                                                                    *)
(*  THE FINITE-PRIME PRODUCT of the local-global Galois connection.   *)
(*                                                                    *)
(*  BiView.v gave the connection at ONE prime (valuation Z  ⊣  local  *)
(*  Q, via inject_Z / Qfloor).  Here we take the PRODUCT over a set   *)
(*  `Idx` of primes: a product of Galois connections is a Galois      *)
(*  connection.  Everything is a pointwise lift of BiView, so it stays *)
(*  axiom-free (no Reals, no topology).                               *)
(*                                                                    *)
(*    - GLOBAL: Idx -> Z, the exponent/valuation VECTOR; the product   *)
(*      order (componentwise <=) IS the DIVISIBILITY order, and        *)
(*      componentwise min/max are gcd/lcm -- the divisibility LATTICE. *)
(*    - LOCAL:  Idx -> Q, the archimedean coordinate at each place.    *)
(*    - alphaP = componentwise inject_Z, gammaP = componentwise Qfloor. *)
(*                                                                    *)
(*  The shared reflection (global complement <-> local 1-s) lifts      *)
(*  componentwise, with an independent resolution per prime.          *)
(*                                                                    *)
(*  `Idx` is abstract (the finite set of primes); finiteness is not    *)
(*  used by the order-theoretic content, so we leave it a parameter.   *)
(* ================================================================= *)

From Stdlib Require Import ZArith QArith Qround Lqa Lia.
Require Import BiView.
Open Scope Q_scope.

Section Product.

Variable Idx : Type.   (* the (finite) set of primes / places *)

(* global valuation vectors and local coordinate vectors *)
Definition GVec := Idx -> Z.
Definition LVec := Idx -> Q.

(* product orders: componentwise.  gle IS the divisibility order.     *)
Definition gle (f g : GVec) : Prop := forall i, (f i <= g i)%Z.
Definition lle (f g : LVec) : Prop := forall i, f i <= g i.

(* the product connection: componentwise inject_Z / Qfloor *)
Definition alphaP (f : GVec) : LVec := fun i => alpha (f i).
Definition gammaP (g : LVec) : GVec := fun i => gamma (g i).

(* ----------------------------------------------------------------- *)
(* SECTION 1 — the product is a Galois connection                    *)
(* ----------------------------------------------------------------- *)

Theorem galois_product : forall f g, gle f (gammaP g) <-> lle (alphaP f) g.
Proof.
  intros f g; unfold gle, lle, alphaP, gammaP; split; intros H i.
  - apply (proj1 (galois_connection (f i) (g i))); apply H.
  - apply (proj2 (galois_connection (f i) (g i))); apply H.
Qed.

Theorem alphaP_monotone : forall f f', gle f f' -> lle (alphaP f) (alphaP f').
Proof. intros f f' H i; unfold alphaP; apply alpha_monotone; apply H. Qed.

Theorem gammaP_monotone : forall g g', lle g g' -> gle (gammaP g) (gammaP g').
Proof. intros g g' H i; unfold gammaP; apply gamma_monotone; apply H. Qed.

(* the global vector round-trips (a retract) *)
Theorem gammaP_alphaP : forall f i, gammaP (alphaP f) i = f i.
Proof. intros f i; unfold gammaP, alphaP; apply gamma_alpha. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — the divisibility lattice: min = gcd, max = lcm        *)
(* ----------------------------------------------------------------- *)

Theorem gle_refl : forall f, gle f f.
Proof. intros f i; apply Z.le_refl. Qed.

Theorem gle_trans : forall f g h, gle f g -> gle g h -> gle f h.
Proof. intros f g h Hfg Hgh i; apply (Z.le_trans _ (g i)); [ apply Hfg | apply Hgh ]. Qed.

Definition gmeet (f g : GVec) : GVec := fun i => Z.min (f i) (g i).  (* gcd *)
Definition gjoin (f g : GVec) : GVec := fun i => Z.max (f i) (g i).  (* lcm *)

Theorem gmeet_le_l : forall f g, gle (gmeet f g) f.
Proof. intros f g i; apply Z.le_min_l. Qed.

Theorem gmeet_le_r : forall f g, gle (gmeet f g) g.
Proof. intros f g i; apply Z.le_min_r. Qed.

(* gmeet is the greatest lower bound (gcd) *)
Theorem gmeet_glb : forall f g h, gle h f -> gle h g -> gle h (gmeet f g).
Proof. intros f g h Hf Hg i; apply Z.min_glb; [ apply Hf | apply Hg ]. Qed.

Theorem gjoin_le_l : forall f g, gle f (gjoin f g).
Proof. intros f g i; apply Z.le_max_l. Qed.

Theorem gjoin_le_r : forall f g, gle g (gjoin f g).
Proof. intros f g i; apply Z.le_max_r. Qed.

(* gjoin is the least upper bound (lcm) *)
Theorem gjoin_lub : forall f g h, gle f h -> gle g h -> gle (gjoin f g) h.
Proof. intros f g h Hf Hg i; apply Z.max_lub; [ apply Hf | apply Hg ]. Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — the shared reflection, per prime                      *)
(* ----------------------------------------------------------------- *)

Definition LrefP (q : LVec) : LVec := fun i => Lref (q i).
Definition GrefP (nv : Idx -> nat) (f : GVec) : GVec := fun i => Gref (nv i) (f i).
Definition densP (nv : Idx -> nat) (f : GVec) : LVec := fun i => dens (nv i) (f i).

(* the global complement maps, componentwise, to the local reflection *)
Theorem shared_reflection_product :
  forall (nv : Idx -> nat) (f : GVec),
  (forall i, (0 < nv i)%nat) ->
  forall i, densP nv (GrefP nv f) i == LrefP (densP nv f) i.
Proof.
  intros nv f Hpos i; unfold densP, GrefP, LrefP.
  exact (shared_reflection (nv i) (Hpos i) (f i)).
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the product connection                           *)
(* ----------------------------------------------------------------- *)

Theorem biview_product :
  (* product Galois connection + monotonicity + retract *)
  (forall f g, gle f (gammaP g) <-> lle (alphaP f) g)
  /\ (forall f f', gle f f' -> lle (alphaP f) (alphaP f'))
  /\ (forall g g', lle g g' -> gle (gammaP g) (gammaP g'))
  /\ (forall f i, gammaP (alphaP f) i = f i)
  (* divisibility lattice: gcd = glb, lcm = lub *)
  /\ (forall f g h, gle h f -> gle h g -> gle h (gmeet f g))
  /\ (forall f g h, gle f h -> gle g h -> gle (gjoin f g) h)
  (* shared reflection, per prime *)
  /\ (forall (nv : Idx -> nat) (f : GVec), (forall i, (0 < nv i)%nat) ->
        forall i, densP nv (GrefP nv f) i == LrefP (densP nv f) i).
Proof.
  split; [ exact galois_product | ].
  split; [ exact alphaP_monotone | ].
  split; [ exact gammaP_monotone | ].
  split; [ exact gammaP_alphaP | ].
  split; [ exact gmeet_glb | ].
  split; [ exact gjoin_lub | exact shared_reflection_product ].
Qed.

End Product.

Print Assumptions biview_product.

(* ================================================================= *)
(*  END BiViewProduct.v                                               *)
(*  The finite-prime product of the local-global Galois connection:    *)
(*  the divisibility lattice (gcd/lcm) adjoint to the local coordinate *)
(*  at each place, with the shared reflection lifting componentwise.   *)
(*  ZERO Admitted; no Reals axioms, no topology.                      *)
(* ================================================================= *)
