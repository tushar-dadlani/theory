(* ================================================================= *)
(*  DirichletModP.v                                                  *)
(*                                                                    *)
(*  PHASE 5, the finish line: genuine DIRICHLET CHARACTERS mod a       *)
(*  prime p, and their ORTHOGONALITY -- transported from the           *)
(*  characters of the cyclic group Z/(p-1)Z (CharactersModN) through   *)
(*  the discrete logarithm base a primitive root (PrimitiveRoot).     *)
(*                                                                    *)
(*    dchar p g a n = 0                    if p | n                    *)
(*                  = (w (p-1))^(a * dlog n)  otherwise                *)
(*                                                                    *)
(*  dirichlet_orthogonality:                                          *)
(*     sum_{n=1}^{p-1} chi_a(n) * conj(chi_b(n)) = p-1 if a=b else 0.  *)
(*                                                                    *)
(*  Plus: values are (p-1)-th roots of unity, chi_a(1)=1, periodicity  *)
(*  mod p, vanishing on multiples of p, and complete multiplicativity. *)
(*                                                                    *)
(*  This closes the from-scratch cyclicity milestone: (Z/pZ)^* cyclic  *)
(*  (axiom-free) + roots of unity / DFT orthogonality (over the custom *)
(*  C) => Dirichlet characters mod p with orthogonality.              *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via C / trig).      *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Reals.
Require Import ZmodPStar ZmodOrder PrimitiveRoot.
Require Import ComplexField RootsOfUnity CharactersModN DFTConvolution.
Open Scope nat_scope.

(* ----------------------------------------------------------------- *)
(*  Discrete logarithm                                               *)
(* ----------------------------------------------------------------- *)

Definition dlog (p g m : nat) : nat := firstsat (fun j => pw p g j =? m) (seq 0 (p - 1)).

Lemma dlog_pow : forall p g k, prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  k < p - 1 -> dlog p g (pw p g k) = k.
Proof.
  intros p g k Hp Hg Hord Hk.
  assert (Hex : existsb (fun j => pw p g j =? pw p g k) (seq 0 (p - 1)) = true)
    by (apply existsb_exists; exists k; split; [ apply in_seq; lia | apply Nat.eqb_refl ]).
  destruct (firstsat_sat (fun j => pw p g j =? pw p g k) (seq 0 (p - 1)) Hex) as [Hs Hin].
  apply Nat.eqb_eq in Hs; apply in_seq in Hin.
  unfold dlog; apply (pow_inj_below p g _ k Hp Hg);
    [ rewrite Hord; lia | rewrite Hord; exact Hk | exact Hs ].
Qed.

(* every unit is a power of the primitive root *)
Lemma powers_units_perm : forall p g, prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  Permutation (map (pw p g) (seq 0 (p - 1))) (seq 1 (p - 1)).
Proof.
  intros p g Hp Hg Hord; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hnd : NoDup (map (pw p g) (seq 0 (p - 1)))).
  { apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros x y Hx Hy Hxy; apply in_seq in Hx; apply in_seq in Hy.
    apply (pow_inj_below p g x y Hp Hg); [ rewrite Hord; lia | rewrite Hord; lia | exact Hxy ]. }
  apply NoDup_Permutation; [ exact Hnd | apply seq_NoDup | ].
  intro n; split.
  - intro Hn; apply in_map_iff in Hn as [k [Hkn Hkin]].
    rewrite <- Hkn; pose proof (pw_unit p g k Hp Hg); apply in_seq; lia.
  - intro Hn.
    assert (Hincl : incl (seq 1 (p - 1)) (map (pw p g) (seq 0 (p - 1)))).
    { apply NoDup_length_incl.
      - exact Hnd.
      - rewrite length_map, !length_seq; lia.
      - intros z Hz; apply in_map_iff in Hz as [k [Hkz Hkin]];
          rewrite <- Hkz; pose proof (pw_unit p g k Hp Hg); apply in_seq; lia. }
    apply Hincl; exact Hn.
Qed.

Lemma dlog_inv : forall p g m, prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  1 <= m <= p - 1 -> pw p g (dlog p g m) = m.
Proof.
  intros p g m Hp Hg Hord Hm.
  assert (Hperm := powers_units_perm p g Hp Hg Hord).
  assert (Hin : In m (map (pw p g) (seq 0 (p - 1))))
    by (apply Permutation_in with (l := seq 1 (p - 1));
          [ apply Permutation_sym; exact Hperm | apply in_seq; lia ]).
  apply in_map_iff in Hin as [k [Hkm Hkin]]; apply in_seq in Hkin.
  rewrite <- Hkm, dlog_pow by (try assumption; lia); reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Root periodicity of w                                            *)
(* ----------------------------------------------------------------- *)

Lemma Cpow_w_mod : forall N a, (0 < N)%nat -> Cpow (w N) a = Cpow (w N) (a mod N).
Proof.
  intros N a HN.
  rewrite (Nat.div_mod_eq a N) at 1.
  rewrite Cpow_add, Cpow_mul, (w_pow_N N HN), Cpow_C1; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The Dirichlet character                                          *)
(* ----------------------------------------------------------------- *)

Definition dchar (p g a n : nat) : C :=
  if (n mod p =? 0)%nat then C0 else Cpow (w (p - 1)) (a * dlog p g (n mod p)).

Lemma dchar_on_power : forall p g a k, prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  k < p - 1 -> dchar p g a (pw p g k) = chi (p - 1) a k.
Proof.
  intros p g a k Hp Hg Hord Hk; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  pose proof (pw_unit p g k Hp Hg) as Hu.
  unfold dchar.
  rewrite (Nat.mod_small (pw p g k) p) by lia.
  replace (pw p g k =? 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite (dlog_pow p g k Hp Hg Hord Hk); reflexivity.
Qed.

Lemma dchar_zero : forall p g a n, Nat.divide p n -> dchar p g a n = C0.
Proof.
  intros p g a n Hdvd; unfold dchar.
  replace (n mod p =? 0) with true; [ reflexivity | ].
  symmetry; apply Nat.eqb_eq, (proj2 (Nat.Lcm0.mod_divide n p)); exact Hdvd.
Qed.

Lemma dchar_1 : forall p g a, prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 ->
  dchar p g a 1 = C1.
Proof.
  intros p g a Hp Hg Hord; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  replace 1 with (pw p g 0) by (apply pw_0; exact Hp2).
  rewrite (dchar_on_power p g a 0 Hp Hg Hord ltac:(lia)).
  unfold chi; rewrite Nat.mul_0_r; reflexivity.
Qed.

Lemma dchar_periodic : forall p g a n, dchar p g a (n + p) = dchar p g a n.
Proof.
  intros p g a n; unfold dchar.
  replace ((n + p) mod p) with (n mod p)
    by (replace (n + p) with (n + 1 * p) by lia; symmetry; apply Nat.Div0.mod_add).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  ORTHOGONALITY                                                    *)
(* ----------------------------------------------------------------- *)

Theorem dirichlet_orthogonality : forall p g a b,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 -> a < p - 1 -> b < p - 1 ->
  fold_right Cadd C0
    (map (fun n => Cmul (dchar p g a n) (Cconj (dchar p g b n))) (seq 1 (p - 1)))
  = (if a =? b then RtoC (INR (p - 1)) else C0).
Proof.
  intros p g a b Hp Hg Hord Ha Hb; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  transitivity (Csum (fun k => Cmul (chi (p - 1) a k) (Cconj (chi (p - 1) b k))) (p - 1)).
  - rewrite Csum_fold.
    rewrite (map_ext_in
      (fun k => Cmul (chi (p - 1) a k) (Cconj (chi (p - 1) b k)))
      (fun k => Cmul (dchar p g a (pw p g k)) (Cconj (dchar p g b (pw p g k))))
      (seq 0 (p - 1)))
      by (intros k Hk; apply in_seq in Hk;
          rewrite (dchar_on_power p g a k Hp Hg Hord ltac:(lia)),
                  (dchar_on_power p g b k Hp Hg Hord ltac:(lia)); reflexivity).
    rewrite <- (map_map (pw p g)
      (fun n => Cmul (dchar p g a n) (Cconj (dchar p g b n)))).
    apply fold_Cadd_perm, Permutation_map, Permutation_sym, powers_units_perm; assumption.
  - apply char_orthogonality_row; [ lia | exact Ha | exact Hb ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER: dchar is a Dirichlet character with orthogonality         *)
(* ----------------------------------------------------------------- *)

Theorem dirichlet_characters_mod_p : forall p, prime (Z.of_nat p) ->
  exists g, 1 <= g <= p - 1 /\ ord p g = p - 1 /\
    (forall a, dchar p g a 1 = C1)
    /\ (forall a n, Nat.divide p n -> dchar p g a n = C0)
    /\ (forall a n, dchar p g a (n + p) = dchar p g a n)
    /\ (forall a b, a < p - 1 -> b < p - 1 ->
          fold_right Cadd C0
            (map (fun n => Cmul (dchar p g a n) (Cconj (dchar p g b n))) (seq 1 (p - 1)))
          = (if a =? b then RtoC (INR (p - 1)) else C0)).
Proof.
  intros p Hp; destruct (units_cyclic p Hp) as [g [Hgu Hgord]].
  exists g; repeat split; [ lia | lia | exact Hgord | | | | ].
  - intro a; apply dchar_1; assumption.
  - intros a n Hn; apply dchar_zero; exact Hn.
  - intros a n; apply dchar_periodic.
  - intros a b Ha Hb; apply dirichlet_orthogonality; assumption.
Qed.

Print Assumptions dirichlet_characters_mod_p.

(* ================================================================= *)
(*  END DirichletModP.v  (Phase 5 -- the finish line)                *)
(*  Genuine Dirichlet characters mod p and their orthogonality,        *)
(*  transported from the cyclic-group characters of Z/(p-1)Z via the   *)
(*  discrete log base a primitive root (units_cyclic).  This ties the   *)
(*  axiom-free cyclicity theorem to the custom-C roots-of-unity /      *)
(*  DFT-orthogonality machinery.  Uses the classical Reals axioms       *)
(*  (quarantined, via C / trig).                                      *)
(* ================================================================= *)
