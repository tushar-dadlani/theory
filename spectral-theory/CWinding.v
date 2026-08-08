(* ================================================================= *)
(*  CWinding.v  —  Milestone C, brick C2c: the winding integral         *)
(*  ∮_{|z|=r} dz/z = 2πi.                                               *)
(*                                                                    *)
(*  On the circle z = r e^{iθ}, the integrand (1/z)·z' = (1/z)·(iz) = i  *)
(*  is the constant Ci, so the contour integral over [0,2π] is 2πi.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2
        CPathIntegral CSegInt.
Open Scope R_scope.

(* the finite integral of a constant *)
Lemma Cintf_const_ab : forall k Hk a b,
  Cintf (fun _ => k) Hk a b = Cmul (RtoC (b - a)) k.
Proof.
  intros k Hk a b; apply Ceq; unfold Cmul, RtoC; cbn [Re Im].
  - transitivity (Re k * (b - a));
      [ exact (RiemannInt_P15 (cont_RI _ (proj1 Hk) a b)) | ring ].
  - transitivity (Im k * (b - a));
      [ exact (RiemannInt_P15 (cont_RI _ (proj2 Hk) a b)) | ring ].
Qed.

(* on the circle, (1/z)·z' collapses to the constant i *)
Lemma arc_over_id : forall r θ, 0 < r ->
  Cmul (Cinv (arc r θ)) (arc' r θ) = Ci.
Proof.
  intros r θ Hr; pose proof (sin2_cos2 θ) as Hsc; unfold Rsqr in Hsc.
  assert (HD : r * cos θ * (r * cos θ) + r * sin θ * (r * sin θ) = r * r) by nra.
  unfold Cmul, Cinv, arc, arc', Cnorm2, Ci; apply Ceq; cbn.
  - rewrite HD; field; nra.
  - rewrite HD.
    replace (r * cos θ / (r * r) * (r * cos θ)
             + - (r * sin θ) / (r * r) * - (r * sin θ))
      with (cos θ * cos θ + sin θ * sin θ) by (field; nra).
    nra.
Qed.

Lemma arc_int_cont : forall r, 0 < r ->
  Ccont (fun u => Cmul (Cinv (arc r u)) (arc' r u)).
Proof.
  intros r Hr.
  replace (fun u => Cmul (Cinv (arc r u)) (arc' r u)) with (fun _ : R => Ci)
    by (apply functional_extensionality; intro u; symmetry; apply arc_over_id; exact Hr).
  apply Ccont_const.
Qed.

Theorem winding_dz_z : forall r (Hr : 0 < r)
  (Hf : Ccont (fun u => Cmul (Cinv (arc r u)) (arc' r u))),
  pathint (arc r) (arc' r) Cinv Hf 0 (2 * PI) = mkC 0 (2 * PI).
Proof.
  intros r Hr Hf; unfold pathint.
  transitivity (Cintf (fun _ => Ci) (Ccont_const Ci) 0 (2 * PI)).
  - apply Cintf_ext; intro u; apply arc_over_id; exact Hr.
  - rewrite Cintf_const_ab; unfold Cmul, RtoC, Ci; apply Ceq; cbn; ring.
Qed.

Print Assumptions winding_dz_z.

(* ================================================================= *)
(*  END CWinding.v  —  ∮_{|z|=r} dz/z = 2πi  (C2c).                     *)
(* ================================================================= *)
