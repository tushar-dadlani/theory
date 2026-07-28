(* ================================================================= *)
(*  DominatingModulus.v  —  ℵ₀ < 𝔟 ≤ 𝔡  (the first cardinal invariants*)
(*  above ℵ₀), via the CReal convergence modulus.                    *)
(*                                                                    *)
(*  A constructive real (`CRealCv.cvQ_of_regular`) carries an EXPLICIT *)
(*  Cauchy MODULUS — a function `precision ↦ index` (≅ ℕ → ℕ) giving   *)
(*  the rate of convergence.  The eventual-domination order on these   *)
(*  moduli,  f ≤* g  :=  ∃N, ∀n≥N, f n ≤ g n,  is exactly the order    *)
(*  the BOUNDING and DOMINATING numbers live on:                      *)
(*                                                                    *)
(*     𝔟 = least size of a ≤*-UNBOUNDED family                        *)
(*     𝔡 = least size of a ≤*-DOMINATING (cofinal) family             *)
(*                                                                    *)
(*  We prove the ZFC backbone — the diagonal lower bounds — axiom-     *)
(*  free:                                                             *)
(*                                                                    *)
(*   • countable_family_bounded : every COUNTABLE family {fᵢ} of       *)
(*        moduli is dominated by a single g  ⟹  no countable family    *)
(*        is unbounded  ⟹  ℵ₀ < 𝔟.                                    *)
(*   • no_countable_dominating : no countable family is dominating     *)
(*        ⟹  ℵ₀ < 𝔡.                                                  *)
(*                                                                    *)
(*  The witness is the windowed-max diagonal  g n = 1 + max_{i≤n} fᵢ n *)
(*  — the same "escape past every listed function" move as Cantor's    *)
(*  diagonal (which gave the TOP endpoint 𝔠 = |ℤ₂| in                 *)
(*  PadicUncountable).  Reading: no countable set of convergence       *)
(*  gauges converges every CReal — the constructive shadow of 𝔡 > ℵ₀. *)
(*                                                                    *)
(*  AXIOM-FREE (Closed under the global context).                    *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia.

(* eventual domination  f ≤* g  on Baire space ℕ→ℕ (moduli) *)
Definition dominates (g f : nat -> nat) : Prop :=
  exists N : nat, forall n : nat, (N <= n)%nat -> (f n <= g n)%nat.

(* max over the window {0,…,k} of a nat sequence *)
Fixpoint bigmax (h : nat -> nat) (k : nat) : nat :=
  match k with O => h O | S k' => Nat.max (bigmax h k') (h k) end.

Lemma bigmax_ge : forall h k i, (i <= k)%nat -> (h i <= bigmax h k)%nat.
Proof.
  intros h k; induction k as [|k IH]; intros i Hi; cbn [bigmax].
  - assert (i = 0)%nat by lia; subst; apply Nat.le_refl.
  - destruct (Nat.eq_dec i (S k)) as [-> | Hne].
    + apply Nat.le_max_r.
    + apply Nat.le_trans with (bigmax h k); [ apply IH; lia | apply Nat.le_max_l ].
Qed.

(* the diagonal modulus that escapes an enumerated family *)
Definition diag (Fam : nat -> (nat -> nat)) (n : nat) : nat :=
  S (bigmax (fun i => Fam i n) n).

(* ================================================================= *)
(*  ℵ₀ < 𝔟 :  every COUNTABLE family of moduli is bounded.           *)
(* ================================================================= *)
Theorem countable_family_bounded : forall (Fam : nat -> (nat -> nat)),
  exists g, forall i, dominates g (Fam i).
Proof.
  intros Fam; exists (diag Fam); intro i.
  exists i; intros n Hin; unfold diag.
  apply Nat.le_le_succ_r, (bigmax_ge (fun j => Fam j n) n i Hin).
Qed.

(* ================================================================= *)
(*  ℵ₀ < 𝔡 :  no COUNTABLE family of moduli is dominating.           *)
(* ================================================================= *)
Definition dominating (D : nat -> (nat -> nat)) : Prop :=
  forall f, exists i, dominates (D i) f.

Theorem no_countable_dominating : forall D, ~ dominating D.
Proof.
  intros D Hdom.
  (* a single g dominates every member D i *)
  destruct (countable_family_bounded D) as [g Hg].
  (* the strictly-larger gauge S∘g must be dominated by some D i … *)
  destruct (Hdom (fun n => S (g n))) as [i Hi]; destruct Hi as [N1 HN1].
  (* … but D i ≤* g, so S∘g ≤* g — impossible at a large enough point *)
  destruct (Hg i) as [N2 HN2].
  specialize (HN1 (Nat.max N1 N2) (Nat.le_max_l _ _)).
  specialize (HN2 (Nat.max N1 N2) (Nat.le_max_r _ _)).
  lia.
Qed.

Print Assumptions countable_family_bounded.
Print Assumptions no_countable_dominating.

(* ================================================================= *)
(*  END DominatingModulus.v                                          *)
(*  The bounding/dominating numbers on the CReal convergence modulus  *)
(*  exceed ℵ₀ (countable families are bounded / never dominating),    *)
(*  by the windowed-max diagonal.  With the endpoints ℵ₀ (countability*)
(*  engines) and 𝔠 = |ℤ₂| (PadicUncountable), this is the first       *)
(*  cardinal invariant strictly inside (ℵ₀, 𝔠].  Axiom-free.          *)
(* ================================================================= *)
