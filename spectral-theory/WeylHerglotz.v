(* ================================================================= *)
(*  WeylHerglotz.v                                                    *)
(*                                                                    *)
(*  The Weyl / Cayley map is a genuine CAYLEY TRANSFORM OF A HERGLOTZ  *)
(*  (Nevanlinna) FUNCTION, and a BIJECTION  R <-> U(1)\{1}.            *)
(*                                                                    *)
(*  HERGLOTZ DICHOTOMY (cayley_herglotz / _lower / cayley_maps_unit):  *)
(*     Im z > 0  ->  |cayley z| < 1     (upper half-plane -> disk)     *)
(*     Im z = 0  ->  |cayley z| = 1     (real axis -> unit circle)     *)
(*     Im z < 0  ->  |cayley z| > 1     (lower half-plane -> exterior) *)
(*  This is exactly the property certifying the boundary-triple Weyl   *)
(*  function as (the Cayley transform of) a Herglotz function.         *)
(*                                                                    *)
(*  ROUND-TRIPS / BIJECTION:                                          *)
(*     icayley (cayley (RtoC t)) = RtoC t         (left inverse)       *)
(*     cayley (icayley u) = u   (u in U(1), u<>1)   (right inverse)    *)
(*     cayley (RtoC .) is injective on R,  and surjective onto         *)
(*     U(1)\{1} with real preimage ext_point u.                        *)
(*                                                                    *)
(*  Consequence for the spectrum: the phase-matching                   *)
(*  cayley(RtoC t) = u is a genuine bijection between ordinates t and  *)
(*  extension phases u <> 1, so the extension parameter is a faithful  *)
(*  coordinate on the spectral axis.                                   *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField SelfAdjointExtension.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  Herglotz / Nevanlinna dichotomy of the Cayley map            *)
(* ----------------------------------------------------------------- *)

(* z + i never vanishes off the point -i (in particular for Im z >= 0). *)
Lemma z_plus_i_ne : forall z, Im z <> -1 -> Cadd z Ci <> C0.
Proof.
  intros z Hz H. apply Hz. apply (f_equal Im) in H.
  unfold Cadd, Ci, C0 in H; cbn [Re Im] in H; lra.
Qed.

(* upper half-plane maps strictly inside the unit disk. *)
Theorem cayley_herglotz : forall z, 0 < Im z -> Cnorm2 (cayley z) < 1.
Proof.
  intros z Hz.
  assert (Hzi : Cadd z Ci <> C0) by (apply z_plus_i_ne; lra).
  assert (Hpos : 0 < Cnorm2 (Cadd z Ci))
    by (unfold Cnorm2, Cadd, Ci; cbn [Re Im]; nra).
  unfold cayley, Cdiv. rewrite Cnorm2_mul, Cnorm2_inv by exact Hzi.
  apply Rmult_lt_reg_r with (r := Cnorm2 (Cadd z Ci)); [ exact Hpos | ].
  rewrite Rmult_assoc, Rinv_l by lra.
  rewrite Rmult_1_r, Rmult_1_l.
  unfold Cnorm2, Cminus, Cadd, Ci; cbn [Re Im]; nra.
Qed.

(* lower half-plane (off the pole z = -i) maps strictly outside the disk. *)
Theorem cayley_herglotz_lower : forall z, Im z < 0 -> Im z <> -1 ->
  1 < Cnorm2 (cayley z).
Proof.
  intros z Hz Hz1.
  assert (Hzi : Cadd z Ci <> C0) by (apply z_plus_i_ne; exact Hz1).
  assert (Hpos : 0 < Cnorm2 (Cadd z Ci)).
  { pose proof (Cnorm2_nonneg (Cadd z Ci)) as Hnn.
    pose proof (Cnorm2_neq_0 (Cadd z Ci) Hzi) as Hne0.
    unfold Cnorm2 in *; lra. }
  unfold cayley, Cdiv. rewrite Cnorm2_mul, Cnorm2_inv by exact Hzi.
  apply Rmult_lt_reg_r with (r := Cnorm2 (Cadd z Ci)); [ exact Hpos | ].
  rewrite Rmult_assoc, Rinv_l by lra.
  rewrite Rmult_1_r, Rmult_1_l.
  unfold Cnorm2, Cminus, Cadd, Ci; cbn [Re Im]; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Round-trips:  cayley and icayley are mutually inverse        *)
(* ----------------------------------------------------------------- *)

(* left inverse: icayley o cayley = id on the real axis. *)
Theorem icayley_cayley : forall t, icayley (cayley (RtoC t)) = RtoC t.
Proof.
  intro t.
  unfold icayley, cayley, Cdiv, Cmul, Cadd, Cminus, Cinv, Cnorm2, Ci, C1, RtoC;
    apply Ceq; cbn [Re Im]; field; nra.
Qed.

(* right inverse: cayley o icayley = id on U(1) \ {1}. *)
Theorem cayley_icayley : forall u, U1 u -> u <> C1 -> cayley (icayley u) = u.
Proof.
  intros u HU Hu. unfold U1, Cnorm2 in HU.
  assert (Hd : (1 - Re u) * (1 - Re u) + - Im u * - Im u <> 0).
  { intro Hz; apply Hu; apply Ceq; simpl; nra. }
  unfold cayley, icayley, Cdiv, Cmul, Cadd, Cminus, Cinv, Cnorm2, Ci, C1;
    apply Ceq; cbn [Re Im]; field; repeat split;
    first
      [ exact Hd
      | match goal with
        | |- ?E <> 0 =>
            replace E with (4 * ((1 - Re u) * (1 - Re u) + - Im u * - Im u))
              by ring;
            intro HH; apply Hd; lra
        end ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  Bijection  R <-> U(1)\{1}                                     *)
(* ----------------------------------------------------------------- *)

(* injective on the real axis. *)
Corollary cayley_RtoC_inj : forall t1 t2,
  cayley (RtoC t1) = cayley (RtoC t2) -> t1 = t2.
Proof.
  intros t1 t2 H.
  assert (Hi : icayley (cayley (RtoC t1)) = icayley (cayley (RtoC t2)))
    by (rewrite H; reflexivity).
  rewrite !icayley_cayley in Hi.
  apply (f_equal Re) in Hi; unfold RtoC in Hi; cbn [Re] in Hi; exact Hi.
Qed.

(* surjective onto U(1)\{1}: every unit phase u <> 1 is cayley of the   *)
(* real point ext_point u. *)
Corollary cayley_surj_unit : forall u, U1 u -> u <> C1 ->
  cayley (RtoC (ext_point u)) = u.
Proof.
  intros u HU Hne.
  rewrite <- (icayley_is_real_point u HU Hne).
  apply cayley_icayley; assumption.
Qed.

(* Packaged: on U(1)\{1} the extension phase and the ordinate are in     *)
(* faithful (bijective) correspondence via cayley / ext_point.          *)
Corollary phase_ordinate_bijection : forall u, U1 u -> u <> C1 ->
  cayley (RtoC (ext_point u)) = u /\
  (forall t, cayley (RtoC t) = u -> t = ext_point u).
Proof.
  intros u HU Hne. split.
  - apply cayley_surj_unit; assumption.
  - intros t Ht. apply cayley_RtoC_inj. rewrite Ht.
    symmetry; apply cayley_surj_unit; assumption.
Qed.

Print Assumptions cayley_herglotz.
Print Assumptions icayley_cayley.
Print Assumptions cayley_icayley.
Print Assumptions phase_ordinate_bijection.
