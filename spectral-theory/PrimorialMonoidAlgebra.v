(* ================================================================= *)
(*  PrimorialMonoidAlgebra.v  —  Brick 5:  the primorial crossover.    *)
(*                                                                    *)
(*  Adj handles ONE prime (Brick 3: (Z/p,x) = Adj((Z/p)^x)); it does    *)
(*  NOT commute with products (Brick 2: adj_not_closed_under_product),  *)
(*  and composite moduli are not zero-adjunctions (Brick 3 counterex).  *)
(*  So at a PRIMORIAL modulus the residue monoid algebra factors as a    *)
(*  TENSOR, not another Adj.  The smallest nontrivial case is the        *)
(*  second primorial 6 = 2.3 (primorial_primes 1 = [2;3]):              *)
(*                                                                    *)
(*      Z[M_6]  ~=  Z[M_2] (x) Z[M_3].                                 *)
(*                                                                    *)
(*  Two independent facts compose to this:                             *)
(*   (1) CRT MONOID ISO  M_6 ~= M_2 x M_3  (crt : x |-> (x mod 2, x mod 3)  *)
(*       carries mult-mod-6 to componentwise mult-mod-2/mod-3; bijective *)
(*       on residues, inverse (3a+4b) mod 6 by Bezout).                *)
(*   (2) TENSOR OF ALGEBRAS  Z[M_2 x M_3] ~= Z[M_2] (x) Z[M_3]          *)
(*       -- HopfGroupTensor.gconv_prod_tensor instantiated at M_2,M_3    *)
(*       (currying carries product convolution to the tensor conv).     *)
(*                                                                    *)
(*  Axiom-free (finite verification + the generic, axiom-free tensor).  *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia List Bool ZArith.
Require Import HopfGroupAlgebraGen HopfGroupTensor PrimorialSpectralTheory.
Import ListNotations.
Open Scope nat_scope.

(* the three multiplicative monoid operations *)
Definition op2 (x y : nat) : nat := (x * y) mod 2.
Definition op3 (x y : nat) : nat := (x * y) mod 3.
Definition op6 (x y : nat) : nat := (x * y) mod 6.

(* the CRT map and its Bezout inverse (2^{-1}=2 mod 3, 3^{-1}=1 mod 2) *)
Definition crt (x : nat) : nat * nat := (x mod 2, x mod 3).
Definition crt_inv (p : nat * nat) : nat := (3 * fst p + 4 * snd p) mod 6.

(* the componentwise product monoid op on M_2 x M_3 (= HopfGroupTensor.opAB) *)
Definition cop (p q : nat * nat) : nat * nat :=
  (op2 (fst p) (fst q), op3 (snd p) (snd q)).

(* element lists *)
Definition e2 : list nat := seq 0 2.          (* [0;1] *)
Definition e3 : list nat := seq 0 3.          (* [0;1;2] *)
Definition e6 : list nat := seq 0 6.          (* [0;1;2;3;4;5] *)
Definition eAB : list (nat * nat) := list_prod e2 e3.

Definition pair_eqb (p q : nat * nat) : bool :=
  Nat.eqb (fst p) (fst q) && Nat.eqb (snd p) (snd q).

Lemma pair_eqb_true : forall p q, pair_eqb p q = true -> p = q.
Proof.
  intros [a b] [c d] H; unfold pair_eqb in H; simpl in H.
  apply andb_prop in H; destruct H as [H1 H2].
  apply Nat.eqb_eq in H1, H2; subst; reflexivity.
Qed.

(* ---- (1) the CRT MONOID ISO, verified on the 6-element carrier ---- *)

Lemma crt_hom_check :
  forallb (fun x => forallb (fun y =>
     pair_eqb (crt (op6 x y)) (cop (crt x) (crt y))) e6) e6 = true.
Proof. vm_compute; reflexivity. Qed.

Theorem crt_hom : forall x y, In x e6 -> In y e6 ->
  crt (op6 x y) = cop (crt x) (crt y).
Proof.
  intros x y Hx Hy; apply pair_eqb_true.
  pose proof crt_hom_check as H; rewrite forallb_forall in H.
  specialize (H x Hx); rewrite forallb_forall in H; exact (H y Hy).
Qed.

Lemma crt_inv_crt_check : forallb (fun x => Nat.eqb (crt_inv (crt x)) x) e6 = true.
Proof. vm_compute; reflexivity. Qed.

Theorem crt_inv_crt : forall x, In x e6 -> crt_inv (crt x) = x.
Proof.
  intros x Hx; apply Nat.eqb_eq.
  pose proof crt_inv_crt_check as H; rewrite forallb_forall in H; exact (H x Hx).
Qed.

Lemma crt_crt_inv_check : forallb (fun p => pair_eqb (crt (crt_inv p)) p) eAB = true.
Proof. vm_compute; reflexivity. Qed.

Theorem crt_crt_inv : forall p, In p eAB -> crt (crt_inv p) = p.
Proof.
  intros p Hp; apply pair_eqb_true.
  pose proof crt_crt_inv_check as H; rewrite forallb_forall in H; exact (H p Hp).
Qed.

Theorem crt_monoid_iso :
  (forall x y, In x e6 -> In y e6 -> crt (op6 x y) = cop (crt x) (crt y))
  /\ (forall x, In x e6 -> crt_inv (crt x) = x)
  /\ (forall p, In p eAB -> crt (crt_inv p) = p).
Proof. split; [ exact crt_hom | split; [ exact crt_inv_crt | exact crt_crt_inv ] ]. Qed.

(* ---- (2) the TENSOR of the algebras, at M_2, M_3 ---- *)
(* cop is exactly HopfGroupTensor.opAB op2 op3 (componentwise), so the   *)
(* product monoid whose algebra tensor-factors below IS  M_2 x M_3.      *)

Theorem product_algebra_tensor : forall (f f' : nat * nat -> Z) (g h : nat),
  gconvGH Nat.eqb Nat.eqb e2 e3 op2 op3 f f' (g, h)
  = tconv Nat.eqb Nat.eqb e2 e3 op2 op3
      (fun a b => f (a, b)) (fun a b => f' (a, b)) g h.
Proof. intros f f' g h; apply gconv_prod_tensor. Qed.

(* ---- MASTER THEOREM: the primorial 6 = 2.3 crossover ---- *)

Theorem primorial_tensor_factorization :
  (* (1) M_6 ~= M_2 x M_3 as multiplicative monoids (CRT at the primorial 6) *)
  ( (forall x y, In x e6 -> In y e6 -> crt (op6 x y) = cop (crt x) (crt y))
    /\ (forall x, In x e6 -> crt_inv (crt x) = x)
    /\ (forall p, In p eAB -> crt (crt_inv p) = p) )
  (* (2) Z[M_2 x M_3] ~= Z[M_2] (x) Z[M_3]  (currying carries conv to tconv) *)
  /\ (forall (f f' : nat * nat -> Z) (g h : nat),
        gconvGH Nat.eqb Nat.eqb e2 e3 op2 op3 f f' (g, h)
        = tconv Nat.eqb Nat.eqb e2 e3 op2 op3
            (fun a b => f (a, b)) (fun a b => f' (a, b)) g h).
Proof. split; [ exact crt_monoid_iso | exact product_algebra_tensor ]. Qed.

(* the modulus 6 is exactly the second primorial p_1.p_2 = 2.3 *)
Example primorial_6 : primorial_primes 1 = [2; 3].
Proof. exact primorial_primes_1. Qed.

(* ---- FUNCTORIALITY: fuse the two halves into one term ----
   The CRT bijection reindexes M_6's convolution to that of M_2 x M_3,
   which then tensor-factors -- so Z[M_6]'s convolution IS the tensor
   convolution, transported. *)

Definition gconv6 (a b : nat -> Z) (r : nat) : Z :=
  sumf e6 (fun x => sumf e6 (fun y =>
    if Nat.eqb (op6 x y) r then (a x * b y)%Z else 0%Z)).

(* the CRT bijection reindexes any sum over the 6 residues to a sum over
   M_2 x M_3 (both are the same 6 values, reordered) *)
Lemma reindex6 : forall F : nat -> Z,
  sumf e6 F = sumf eAB (fun p => F (crt_inv p)).
Proof. intros F; unfold sumf, e6, eAB, crt_inv; cbn; ring. Qed.

(* the convolution condition matches under the bijection (216 finite cases) *)
Lemma cond_eq_check :
  forallb (fun p => forallb (fun q => forallb (fun r =>
     Bool.eqb (Nat.eqb (op6 (crt_inv p) (crt_inv q)) (crt_inv r))
              (pair_eqb (cop p q) r)) eAB) eAB) eAB = true.
Proof. vm_compute; reflexivity. Qed.

Lemma cond_eq : forall p q r, In p eAB -> In q eAB -> In r eAB ->
  Nat.eqb (op6 (crt_inv p) (crt_inv q)) (crt_inv r) = pair_eqb (cop p q) r.
Proof.
  intros p q r Hp Hq Hr; apply Bool.eqb_prop.
  pose proof cond_eq_check as H.
  rewrite forallb_forall in H; specialize (H p Hp).
  rewrite forallb_forall in H; specialize (H q Hq).
  rewrite forallb_forall in H; exact (H r Hr).
Qed.

(* M_6's convolution equals M_2 x M_3's, transported along crt *)
Theorem gconv6_eq_gconvGH : forall a b r, In r eAB ->
  gconv6 a b (crt_inv r)
  = gconvGH Nat.eqb Nat.eqb e2 e3 op2 op3
      (fun p => a (crt_inv p)) (fun p => b (crt_inv p)) r.
Proof.
  intros a b r Hr; unfold gconv6, gconvGH.
  rewrite reindex6; apply sumf_ext; intros p Hp.
  rewrite reindex6; apply sumf_ext; intros q Hq.
  change (ABeq Nat.eqb Nat.eqb (opAB op2 op3 p q) r) with (pair_eqb (cop p q) r).
  rewrite (cond_eq p q r Hp Hq Hr); reflexivity.
Qed.

(* ...and that convolution is the tensor conv: the full functorial statement *)
Theorem gconv6_tensor : forall a b g h, In (g, h) eAB ->
  gconv6 a b (crt_inv (g, h))
  = tconv Nat.eqb Nat.eqb e2 e3 op2 op3
      (fun i j => a (crt_inv (i, j))) (fun i j => b (crt_inv (i, j))) g h.
Proof.
  intros a b g h Hgh.
  rewrite (gconv6_eq_gconvGH a b (g, h) Hgh); apply gconv_prod_tensor.
Qed.

Print Assumptions primorial_tensor_factorization.
Print Assumptions gconv6_tensor.

(* ================================================================= *)
(*  END PrimorialMonoidAlgebra.v  (Brick 5: at the primorial 6 = 2.3    *)
(*  the residue monoid algebra factors as a TENSOR Z[M_2] (x) Z[M_3],   *)
(*  not another Adj -- Adj handles one prime, tensor handles many, the  *)
(*  primorial is the crossover.)                                        *)
(* ================================================================= *)
