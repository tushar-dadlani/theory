(* ================================================================= *)
(*  CharModulus.v  --  Dirichlet characters have modulus at most 1.   *)
(*                                                                    *)
(*  The one fact needed to make L(s,chi) converge by comparison with   *)
(*  the p-series: |chi(n)| <= 1.  DirichletModP.dchar is either C0 or  *)
(*  a power of the root of unity w (p-1), so this reduces to           *)
(*  |w N| = 1 -- which, surprisingly, is nowhere in the repo.          *)
(*  (Cmod_wgt, Cmod_arc and clampw_mod are all about other objects.)   *)
(*                                                                    *)
(*  No side condition on N is needed: at N = 0, INR 0 = 0, / 0 = 0,    *)
(*  cos 0 = 1, sin 0 = 0, so |w 0| = 1 as well.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus RootsOfUnity DirichletModP.
Open Scope R_scope.

(* |a^k| = |a|^k -- proved locally to keep this file's dependency cone
   small (CCauchyCont and CCauchyAnalytic each have a copy, but both
   drag in the whole contour tower) *)
Lemma Cmod_C1_loc : Cmod C1 = 1.
Proof.
  unfold Cmod, Cnorm2, C1; cbn [Re Im].
  replace (1 * 1 + 0 * 0) with 1 by ring. apply sqrt_1.
Qed.

Lemma Cmod_Cpow_loc : forall a k, Cmod (Cpow a k) = (Cmod a) ^ k.
Proof.
  intros a k. induction k as [| k IH]; cbn [Cpow pow].
  - apply Cmod_C1_loc.
  - rewrite Cmod_mul, IH. reflexivity.
Qed.

Theorem Cmod_w : forall N, Cmod (w N) = 1.
Proof.
  intro N. unfold Cmod, Cnorm2, w; cbn [Re Im].
  pose proof (sin2_cos2 (2 * PI / INR N)) as H. unfold Rsqr in H.
  replace (cos (2 * PI / INR N) * cos (2 * PI / INR N)
           + sin (2 * PI / INR N) * sin (2 * PI / INR N))
    with (sin (2 * PI / INR N) * sin (2 * PI / INR N)
          + cos (2 * PI / INR N) * cos (2 * PI / INR N)) by ring.
  rewrite H. apply sqrt_1.
Qed.

Theorem Cmod_dchar_le : forall p g a n, Cmod (dchar p g a n) <= 1.
Proof.
  intros p g a n. unfold dchar.
  destruct (n mod p =? 0)%nat.
  - rewrite (proj2 (Cmod0 C0) eq_refl). lra.
  - rewrite Cmod_Cpow_loc, Cmod_w, pow1. lra.
Qed.

(* the character is nonzero exactly off the modulus *)
Theorem Cmod_dchar_1 : forall p g a n, (n mod p =? 0)%nat = false ->
  Cmod (dchar p g a n) = 1.
Proof.
  intros p g a n H. unfold dchar. rewrite H.
  rewrite Cmod_Cpow_loc, Cmod_w, pow1. reflexivity.
Qed.

Print Assumptions Cmod_dchar_le.

(* ================================================================= *)
(*  END CharModulus.v                                                 *)
(* ================================================================= *)
