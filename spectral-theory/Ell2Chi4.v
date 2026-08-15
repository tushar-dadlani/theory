(* ================================================================= *)
(*  Ell2Chi4.v   (a concrete Zhat^x character: the mod-4 character)      *)
(*                                                                    *)
(*  chi4  is the non-principal real primitive Dirichlet character mod 4: *)
(*     chi4(n) = +1 if n = 1 mod 4,  -1 if n = 3 mod 4,  0 if n even.    *)
(*  It is completely multiplicative and unimodular, hence a genuine      *)
(*  element of the character group (the Pontryagin dual of Zhat^x), and  *)
(*  instantiates the abstract Ell2Symmetry.character_symmetry to a       *)
(*  concrete, non-vacuous symmetry of the Bost-Connes spectral triple.   *)
(*  Its twisted partition function is the Dirichlet beta function        *)
(*     Tr(U_{chi4} e^{-b D}) = sum chi4(n) n^{-b} = beta(b)               *)
(*                           = 1 - 3^{-b} + 5^{-b} - 7^{-b} + ...         *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (+ functional_extensionality). *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia.
Require Import Ell2 Ell2Operator Ell2Basis Ell2Zeta Ell2Fock Ell2SpectralTriple
        Ell2Symmetry.
Open Scope R_scope.

(* the mod-4 character *)
Definition chi4 (n : nat) : R :=
  match n mod 4 with
  | 1 => 1
  | 3 => -1
  | _ => 0
  end.

Lemma chi4_1 : chi4 1 = 1.
Proof. reflexivity. Qed.

(* chi4 is non-principal: it takes the value -1 *)
Lemma chi4_nontrivial : chi4 3 = -1.
Proof. reflexivity. Qed.

Lemma chi4_unimod : forall n, Rabs (chi4 n) <= 1.
Proof.
  intro n. unfold chi4. destruct (n mod 4) as [|[|[|[|n']]]];
    unfold Rabs; destruct (Rcase_abs _); lra.
Qed.

(* chi4 is completely multiplicative *)
Lemma chi4_mult : forall m n, chi4 (m * n) = (chi4 m * chi4 n)%R.
Proof.
  intros m n. unfold chi4.
  rewrite Nat.Div0.mul_mod.
  assert (Hm : (m mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hn : (n mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
  destruct (m mod 4) as [|[|[|[|m']]]] eqn:Em; try lia;
    destruct (n mod 4) as [|[|[|[|n']]]] eqn:En; try lia;
    simpl; ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  the concrete symmetry and its Dirichlet-beta partition function     *)
(* ------------------------------------------------------------------ *)

(* the full Ell2Symmetry.character_symmetry, now for a concrete character *)
Theorem chi4_symmetry : forall b, 1 < b ->
  (forall f n, Dop (sym chi4 f) n = sym chi4 (Dop f) n)
  * (forall p m n, (1 <= p)%nat ->
       sym chi4 (crea p (e m)) n = chi4 p * crea p (sym chi4 (e m)) n)
  * { L : R | Un_cv (fun N => diag_trace (fun n => chi4 n * z b n) N) L }.
Proof.
  intros b Hb. exact (character_symmetry chi4 chi4_mult chi4_unimod b Hb).
Qed.

(* the twisted partition function is the Dirichlet beta function:        *)
(*   Tr(U_{chi4} e^{-b D}) = sum chi4(n) n^{-b} = beta(b),  converges b>1 *)
Theorem dirichlet_beta_converges : forall b, 1 < b ->
  { L : R | Un_cv (fun N => diag_trace (fun n => chi4 n * z b n) N) L }.
Proof. intros b Hb. exact (twisted_partition_is_L chi4 chi4_unimod b Hb). Qed.

Print Assumptions chi4_symmetry.
