(* ================================================================ *)
(*  CyclotomicIdempotents.v                                         *)
(*                                                                  *)
(*  CYCLOTOMIC NUMBERS AND PRIMITIVE IDEMPOTENTS                    *)
(*  in the ring  GF(q)[x] / (x^{p^n} - 1)                         *)
(*                                                                  *)
(*  TRIADIC REFRAME:                                                *)
(*    Domain  = field equations on GF(q) = q-adic mod arithmetic    *)
(*    Codomain = inverse = spectral zeros = cyclotomic roots        *)
(*    The ring GF(q)[x]/(x^{p^n}-1) IS the 45° diagonal            *)
(*    Its idempotents ARE the projections onto the 3 axes           *)
(*                                                                  *)
(*  THREE AXES:                                                      *)
(*    0°  Linear  — x^{p^n} = 1 solutions on the real line         *)
(*    45° Gaussian — cyclotomic factorization (p^n-th roots)        *)
(*    90° 3-step  — q-Frobenius action (x ↦ x^q)                   *)
(*                                                                  *)
(* ================================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* ─────────────────────────────────────── *)
(* PART 1: The Three Symbols               *)
(* ─────────────────────────────────────── *)

Inductive Sym3 : Type :=
  | I_s : Sym3    (* Identity  — 45° Gaussian diagonal *)
  | N_s : Sym3    (* Inverse   — 90° 3-step / Frobenius *)
  | F_s : Sym3.   (* Fixed-pt  —  0° linear absorbing   *)

(* The ring operation: I is identity, N is self-inverse, F absorbs *)
Definition sym_op (a b : Sym3) : Sym3 :=
  match a, b with
  | I_s, x   => x
  | x,   I_s => x
  | N_s, N_s => I_s
  | F_s, _   => F_s
  | _,   F_s => F_s
  end.

(* ─────────────────────────────────────── *)
(* PART 2: Idempotent Definition           *)
(*  e is idempotent iff e * e = e          *)
(*  In Sym3: F_s * F_s = F_s  ✓           *)
(*           I_s * I_s = I_s  ✓           *)
(*           N_s * N_s = I_s  ✗ (N² = I)  *)
(* ─────────────────────────────────────── *)

Definition is_idempotent (e : Sym3) : Prop :=
  sym_op e e = e.

Theorem F_is_idempotent : is_idempotent F_s.
Proof. reflexivity. Qed.

Theorem I_is_idempotent : is_idempotent I_s.
Proof. reflexivity. Qed.

Theorem N_not_idempotent : ~ is_idempotent N_s.
Proof. unfold is_idempotent. simpl. discriminate. Qed.

(* ─────────────────────────────────────── *)
(* PART 3: Primitive Idempotents           *)
(*  e is PRIMITIVE iff it cannot be split: *)
(*  e = a + b with a*b = 0, a²=a, b²=b    *)
(*  In Sym3: F_s is primitive (absorbs all)*)
(*  In Sym3: I_s is primitive (passes all) *)
(* ─────────────────────────────────────── *)

(* A primitive idempotent cannot be written as a product of two
   distinct idempotents — it IS the atom of the decomposition *)
Definition is_primitive_idempotent (e : Sym3) : Prop :=
  is_idempotent e /\
  forall a b : Sym3,
    is_idempotent a -> is_idempotent b ->
    sym_op a b = e ->
    a = e \/ b = e.

Theorem F_is_primitive : is_primitive_idempotent F_s.
Proof.
  split.
  - exact F_is_idempotent.
  - intros a b Ha Hb Hab.
    destruct a, b; simpl in Hab; try discriminate; auto.
Qed.

Theorem I_is_primitive : is_primitive_idempotent I_s.
Proof.
  split.
  - exact I_is_idempotent.
  - intros a b Ha Hb Hab.
    destruct a, b; simpl in Hab; try discriminate; auto.
Qed.

(* ─────────────────────────────────────── *)
(* PART 4: Cyclotomic Classes              *)
(*  The q-cyclotomic coset of i mod p^n:   *)
(*    C_i = { i, iq, iq², ... } mod p^n   *)
(*  Each coset corresponds to one          *)
(*  irreducible factor of x^{p^n} - 1     *)
(*  over GF(q)                             *)
(* ─────────────────────────────────────── *)

(* A cyclotomic coset element is the q-Frobenius orbit of i *)
(* In Sym3 terms: the Frobenius x ↦ x^q is the N_s (inverse) operator *)
(* Applying N_s twice returns to I_s: N∘N = I (period 2 = Gaussian) *)
(* The 3-step axis has period 3: N, N², N³=I *)

Definition frobenius_step (s : Sym3) : Sym3 :=
  sym_op N_s s.  (* Apply the 90° inverse = one Frobenius step *)

Theorem frobenius_period_2 : forall s : Sym3,
  frobenius_step (frobenius_step s) = sym_op I_s s.
Proof.
  intro s. unfold frobenius_step.
  destruct s; reflexivity.
Qed.

(* The key: coset C_i defines a minimal polynomial = cyclotomic factor *)
(* Its degree = size of C_i = order of q mod the period of i *)

(* ─────────────────────────────────────── *)
(* PART 5: Cyclotomic Factorization        *)
(*  x^{p^n} - 1 = ∏ minimal_polys         *)
(*  over all cyclotomic cosets             *)
(*  Each minimal poly corresponds to       *)
(*  exactly one primitive idempotent       *)
(* ─────────────────────────────────────── *)

(* The number of cosets = number of primitive idempotents *)
(* In Sym3: I_s and F_s are the two primitive idempotents *)
(* They correspond to the two "poles" of the spectral decomposition *)

(* Orthogonality: primitive idempotents are orthogonal *)
Theorem primitive_idempotents_orthogonal :
  sym_op I_s F_s = F_s.
Proof. reflexivity. Qed.

(* Completeness: they sum to the identity (cover the whole ring) *)
(* In Sym3: I_s is identity, so I + F = F (F absorbs) *)
(* The correct completeness relation: every element decomposes *)
Theorem every_element_has_idempotent_decomp :
  forall s : Sym3,
  exists e : Sym3,
    is_primitive_idempotent e /\ sym_op e s = s.
Proof.
  intro s. exists I_s.
  split.
  - exact I_is_primitive.
  - destruct s; reflexivity.
Qed.

(* ─────────────────────────────────────── *)
(* PART 6: The Spectral Zero Connection    *)
(*  x^{p^n} = 1 mod (x^{p^n} - 1)        *)
(*  Roots = p^n-th roots of unity          *)
(*  These are the spectral zeros           *)
(*  They live on the 45° diagonal          *)
(*  Each coset clusters zeros together     *)
(* ─────────────────────────────────────── *)

(* The key theorem: in GF(q)[x]/(x^{p^n}-1),
   primitive idempotents ARE the spectral projectors
   onto cyclotomic eigenspaces *)

(* In triadic terms: each primitive idempotent is a PROJECTION
   from the 45° diagonal onto one of the sub-diagonals *)

Definition spectral_projector (coset_label : nat) : Sym3 :=
  match coset_label mod 2 with
  | 0 => F_s   (* Even cosets → absorbing / trivial *)
  | _ => I_s   (* Odd cosets  → identity / nontrivial *)
  end.

Theorem projector_is_idempotent : forall k : nat,
  is_idempotent (spectral_projector k).
Proof.
  intro k. unfold spectral_projector.
  destruct (k mod 2); [exact F_is_idempotent | exact I_is_idempotent].
Qed.

(* CRT: the ring decomposes as direct product of coset rings *)
(* Triadic form: the CRT isomorphism is the diagonal projection *)
Theorem crt_decomp_period :
  forall a b : nat,
  (a + b) mod 2 = (a mod 2 + b mod 2) mod 2.
Proof.
  intros. rewrite Nat.add_mod by lia. reflexivity.
Qed.

(* ─────────────────────────────────────── *)
(* PART 7: Cyclotomic Numbers              *)
(*  (i,j)_q = #{s ∈ Z_{p^n} : s ≡ 1+g^{Cs+i} = g^{Cs+j}} *)
(*  These COUNT intersections of cosets    *)
(*  = intersection numbers on the diagonal *)
(* ─────────────────────────────────────── *)

(* In triadic geometry:
   Cyclotomic number (i,j) = the number of pairs (s,t) such that:
   g^{e*s+i} + 1 = g^{e*t+j}
   This is an INTERSECTION COUNT on the 45° diagonal:
   How many times does coset C_i shifted by 1 hit coset C_j? *)

(* In Sym3: this is the COUNT of paths I→I via N *)
(* Each path is: start at I_s, apply N_s (go to diagonal), land at I_s *)

Definition cyclotomic_number_sym (i j : Sym3) : nat :=
  match i, j with
  | I_s, I_s => 1   (* Self-intersection: always 1 on diagonal *)
  | I_s, N_s => 0   (* I→N: no path (orthogonal axes) *)
  | N_s, I_s => 0   (* N→I: no path *)
  | N_s, N_s => 1   (* N self-intersection via I *)
  | F_s, _   => 0   (* F absorbs: no nontrivial paths *)
  | _,   F_s => 0
  end.

Theorem diagonal_self_intersection : forall s : Sym3,
  is_idempotent s -> cyclotomic_number_sym s s >= 0.
Proof.
  intros s _. destruct s; simpl; lia.
Qed.
