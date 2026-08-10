(* ================================================================= *)
(*  ArakelovDegree.v  —  the arithmetic (Arakelov) degree of a          *)
(*  principal divisor on the compactified Spec Z, and its vanishing.     *)
(*                                                                    *)
(*  For a positive rational x = a/b (a = code ps ea, b = code ps eb over *)
(*  a common prime list ps), the ARAKELOV DEGREE of the principal        *)
(*  arithmetic divisor div(x) is the sum of the local log-sizes over all *)
(*  places v of Q (the archimedean place ∞ and one per prime p):         *)
(*                                                                    *)
(*    arith_deg(x)  =  log|x|_∞  +  Σ_p log|x|_p                         *)
(*                  =  ( log a − log b )  +  Σ_i (eb_i − ea_i) log p_i.   *)
(*                                                                    *)
(*  THEOREM  arith_deg(x) = 0  — the additive/logarithmic product        *)
(*  formula (the degree of a principal arithmetic divisor is 0), the     *)
(*  real-analytic sibling of ProductFormulaQ.product_formula_Q           *)
(*  (∏_v |x|_v = 1).  The whole content is `ln_code`: log of the unique  *)
(*  factorization, log(∏_i p_i^{k_i}) = Σ_i k_i·log p_i.  This is the     *)
(*  repo's first Arakelov object.  Axiom-clean (only the 4 real axioms). *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Reals Lra Lia List.
Import ListNotations.
Require Import PrimeFactorizationN.
Open Scope R_scope.

(* IZR is positive on positive integers *)
Lemma IZR_pos : forall z, (0 < z)%Z -> 0 < IZR z.
Proof. intros z Hz; replace 0 with (IZR 0) by reflexivity; apply IZR_lt; lia. Qed.

(* code (∏ p_i^{k_i}) is a positive integer when the p_i are primes *)
Lemma code_pos : forall ps ks, Forall prime ps -> (0 < code ps ks)%Z.
Proof.
  induction ps as [|p ps' IH]; intros ks Hpr.
  - cbn [code]; lia.
  - destruct ks as [|k ks']; [ cbn [code]; lia | ].
    inversion Hpr as [| ? ? Hp Hpr']; subst.
    cbn [code]; apply Z.mul_pos_pos.
    + apply Z.pow_pos_nonneg; [ destruct Hp; lia | lia ].
    + apply IH; exact Hpr'.
Qed.

(* log of a prime power: log(p^k) = k·log p *)
Lemma ln_pow_p : forall p k, (0 < p)%Z ->
  ln (IZR (p ^ Z.of_nat k)) = IZR (Z.of_nat k) * ln (IZR p).
Proof.
  intros p k Hp; induction k as [|k IH].
  - replace (Z.of_nat 0) with 0%Z by reflexivity.
    rewrite Z.pow_0_r; replace (IZR 1) with 1 by reflexivity.
    rewrite ln_1; replace (IZR 0) with 0 by reflexivity; ring.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.pow_add_r by lia.
    rewrite Z.pow_1_r, mult_IZR, ln_mult
      by (apply IZR_pos; try apply Z.pow_pos_nonneg; lia).
    rewrite IH, plus_IZR; replace (IZR 1) with 1 by reflexivity; ring.
Qed.

(* the finite (non-archimedean) log-mass:  Σ_i k_i·log p_i  *)
Definition logsum (ps : list Z) (ks : list nat) : R :=
  fold_right Rplus 0
    (map (fun pk => IZR (Z.of_nat (snd pk)) * ln (IZR (fst pk))) (combine ps ks)).

(* THE key lemma: log of the factorization = Σ exponents · log primes *)
Lemma ln_code : forall ps ks, Forall prime ps -> length ps = length ks ->
  ln (IZR (code ps ks)) = logsum ps ks.
Proof.
  induction ps as [|p ps' IH]; intros ks Hpr Hlen.
  - destruct ks as [|k ks']; [ | simpl in Hlen; lia ].
    cbn [code]; replace (IZR 1) with 1 by reflexivity; rewrite ln_1.
    unfold logsum; reflexivity.
  - destruct ks as [|k ks']; [ simpl in Hlen; lia | ].
    inversion Hpr as [| ? ? Hp Hpr']; subst.
    assert (Hp0 : (0 < p)%Z) by (destruct Hp; lia).
    cbn [code]; rewrite mult_IZR, ln_mult
      by (apply IZR_pos; (apply Z.pow_pos_nonneg; lia) || (apply code_pos; exact Hpr')).
    rewrite (ln_pow_p p k Hp0), (IH ks' Hpr' ltac:(simpl in Hlen; lia)).
    unfold logsum; cbn [combine map fold_right fst snd]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The Arakelov degree of the principal divisor of x = a/b            *)
(* ----------------------------------------------------------------- *)

(* archimedean local degree  log|x|_∞ = log a − log b *)
Definition deg_inf (ps : list Z) (ea eb : list nat) : R :=
  ln (IZR (code ps ea)) - ln (IZR (code ps eb)).

(* finite local degrees  Σ_p log|x|_p = Σ_i (eb_i − ea_i)·log p_i = logsum eb − logsum ea *)
Definition deg_fin (ps : list Z) (ea eb : list nat) : R :=
  logsum ps eb - logsum ps ea.

Definition arith_deg (ps : list Z) (ea eb : list nat) : R :=
  deg_inf ps ea eb + deg_fin ps ea eb.

(* THE PRODUCT FORMULA, additive form: deg of a principal divisor is 0 *)
Theorem arith_deg_zero : forall ps ea eb,
  Forall prime ps -> length ps = length ea -> length ps = length eb ->
  arith_deg ps ea eb = 0.
Proof.
  intros ps ea eb Hpr Hla Hlb.
  unfold arith_deg, deg_inf, deg_fin.
  rewrite (ln_code ps ea Hpr Hla), (ln_code ps eb Hpr Hlb); ring.
Qed.

Print Assumptions arith_deg_zero.

(* ================================================================= *)
(*  END ArakelovDegree.v  —  arith_deg(div x) = 0 on compactified       *)
(*  Spec Z, the additive product formula (sibling of                    *)
(*  ProductFormulaQ.product_formula_Q, ∏_v |x|_v = 1).  The repo's       *)
(*  first Arakelov-degree object.  Axiom-clean.                         *)
(* ================================================================= *)
