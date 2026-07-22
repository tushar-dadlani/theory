(* ================================================================= *)
(*  ProductFormula.v                                                  *)
(*                                                                    *)
(*  The PRODUCT FORMULA as an order/algebra identity on the           *)
(*  divisibility lattice (BiViewProduct's global side), topology-free. *)
(*                                                                    *)
(*  Over a finite list of places, the "degree" (total valuation)      *)
(*     deg L f = sum over the places in L of the valuation f i        *)
(*  satisfies:                                                        *)
(*    - deg_gcd_lcm : deg (gcd) + deg (lcm) = deg a + deg b           *)
(*      -- the additive/valuation form of  gcd(a,b) * lcm(a,b) = a*b   *)
(*      (per place, min + max = a + b), i.e. the multiplicative        *)
(*      "product formula" of the divisibility lattice;                *)
(*    - deg_reflection : deg (complement of f) = (total) - deg f      *)
(*      -- the shared reflection z |-> n - z acts on the degree as     *)
(*      d |-> total - d, an affine involution fixed at total/2.        *)
(*                                                                    *)
(*  Pure Z / lia; axiom-free; no topology.                            *)
(* ================================================================= *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Section PF.

Variable Idx : Type.                 (* the set of places / primes *)
Definition GVec := Idx -> Z.          (* valuation vectors *)

Definition gmeet (f g : GVec) : GVec := fun i => Z.min (f i) (g i).  (* gcd *)
Definition gjoin (f g : GVec) : GVec := fun i => Z.max (f i) (g i).  (* lcm *)
Definition GrefP (nv : Idx -> nat) (f : GVec) : GVec :=
  fun i => (Z.of_nat (nv i) - f i)%Z.                                (* complement *)

(* total valuation / degree over a finite list of places *)
Definition deg (L : list Idx) (f : GVec) : Z :=
  fold_right (fun i acc => f i + acc) 0 L.

(* THE PRODUCT FORMULA (valuation form of gcd(a,b)*lcm(a,b) = a*b):   *)
(* summing min + max = a + b over the places.                         *)
Theorem deg_gcd_lcm : forall L f g,
  deg L (gmeet f g) + deg L (gjoin f g) = deg L f + deg L g.
Proof.
  intros L f g; unfold deg, gmeet, gjoin.
  induction L as [|i L' IH]; simpl; lia.
Qed.

(* the reflection acts on the degree as d |-> (total resolution) - d *)
Theorem deg_reflection : forall L nv f,
  deg L (GrefP nv f) = deg L (fun i => Z.of_nat (nv i)) - deg L f.
Proof.
  intros L nv f; unfold deg, GrefP.
  induction L as [|i L' IH]; simpl; lia.
Qed.

(* degree is additive on the (pointwise) sum, and the complement is an *)
(* involution on it *)
Theorem deg_reflection_involutive : forall L nv f,
  deg L (GrefP nv (GrefP nv f)) = deg L f.
Proof.
  intros L nv f; unfold deg, GrefP.
  induction L as [|i L' IH]; simpl; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER — the product formula, order/algebra form                  *)
(* ----------------------------------------------------------------- *)

Theorem product_formula :
  (* gcd * lcm = a * b, in valuation (additive) form *)
  (forall L f g, deg L (gmeet f g) + deg L (gjoin f g) = deg L f + deg L g)
  (* the reflection acts as d |-> total - d on the degree *)
  /\ (forall L nv f, deg L (GrefP nv f) = deg L (fun i => Z.of_nat (nv i)) - deg L f)
  (* ... and is an involution there *)
  /\ (forall L nv f, deg L (GrefP nv (GrefP nv f)) = deg L f).
Proof.
  split; [ exact deg_gcd_lcm | ].
  split; [ exact deg_reflection | exact deg_reflection_involutive ].
Qed.

End PF.

Print Assumptions product_formula.

(* ================================================================= *)
(*  END ProductFormula.v                                              *)
(*  gcd*lcm = a*b (valuation form) and the reflection d |-> total - d  *)
(*  on the divisibility lattice's degree.  ZERO Admitted; no axioms.  *)
(* ================================================================= *)
