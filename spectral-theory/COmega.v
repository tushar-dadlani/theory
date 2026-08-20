(* ================================================================= *)
(*  COmega.v  —  the CUBE ROOT OF UNITY and its identities.            *)
(*                                                                    *)
(*    om := w 3,  the primitive cube root of unity                     *)
(*    om_one_plus     : 1 + om + om^2 = 0                              *)
(*    quad_factor_gen : (a+ub+u^2c)(a+u^2b+uc) = a^2+b^2+c^2-ab-bc-ca  *)
(*    eisenstein_norm_gen : (a+ub)(a+u^2b) = a^2 - ab + b^2            *)
(*    cube_omega_factor :                                              *)
(*        a^3+b^3+c^3-3abc = (a+b+c)(a+om b+om^2 c)(a+om^2 b+om c)     *)
(*                                                                    *)
(*  RootsOfUnity is already general in N -- w_pow_N, w_primitive,      *)
(*  sum_pow_eq_0, dft_orthogonality all hold for every N -- but w is   *)
(*  only ever instantiated at w p and w (p-1), for the QUADRATIC Gauss *)
(*  sum.  N = 3 is never taken, so 1 + om + om^2 = 0, the identity     *)
(*  every cubic statement rests on, was not available anywhere.        *)
(*                                                                    *)
(*  THE IDENTITIES ARE STATED GENERICALLY IN u, over any root of       *)
(*  1 + u + u^2 = 0, and only afterwards instantiated at om.  That is  *)
(*  not abstraction for its own sake: the generic form is what a       *)
(*  Z[omega] arithmetic layer will need, where the root is a formal    *)
(*  adjoined element rather than a specific complex number.            *)
(*                                                                    *)
(*  eisenstein_norm_gen is exactly the norm form                       *)
(*  crypto/PrimeFactorizationTriadic.eisenstein_norm was defined for   *)
(*  and never given a theorem.                                        *)
(*                                                                    *)
(*  PROOF NOTE.  ring cannot use u^3 = 1, so it would fail on the      *)
(*  factorization directly.  The expansion is therefore done in ONE    *)
(*  ring-checked assert that keeps u^3 and u^4 as explicit products,   *)
(*  and only then are they rewritten by om_cube and u + u^2 = -1.      *)
(*  Likewise 3abc is written (1+1+1)abc rather than RtoC 3, which ring *)
(*  would treat as an opaque atom.  Axiom-clean.                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus RootsOfUnity.
Open Scope R_scope.

Definition om : C := w 3.

(* ----------------------------------------------------------------- *)
(*  A.  the three defining facts                                       *)
(* ----------------------------------------------------------------- *)
Lemma om_ne1 : om <> C1.
Proof.
  pose proof (w_primitive 3 1 ltac:(lia)) as H.
  cbn [Cpow] in H. unfold om. intro Hc. apply H. rewrite Hc. ring.
Qed.

Lemma om_pow3 : Cpow om 3 = C1.
Proof. unfold om. apply w_pow_N. lia. Qed.

Lemma om_one_plus : Cadd C1 (Cadd om (Cmul om om)) = C0.
Proof.
  pose proof (sum_pow_eq_0 om 3 om_ne1 om_pow3) as H.
  cbn [Csum Cpow] in H.
  assert (E : Cadd C1 (Cadd om (Cmul om om))
              = Cadd (Cadd (Cadd C0 C1) (Cmul om C1)) (Cmul om (Cmul om C1)))
    by ring.
  rewrite E. exact H.
Qed.

Lemma om_sq : Cmul om om = Copp (Cadd C1 om).
Proof.
  pose proof om_one_plus as H.
  assert (E : Cmul om om
              = Cminus (Cadd C1 (Cadd om (Cmul om om))) (Cadd C1 om)) by ring.
  rewrite E, H. ring.
Qed.

Lemma om_cube : Cmul om (Cmul om om) = C1.
Proof.
  pose proof om_pow3 as H. cbn [Cpow] in H.
  assert (E : Cmul om (Cmul om om) = Cmul om (Cmul om (Cmul om C1))) by ring.
  rewrite E, H. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the identities, generic in the root                            *)
(* ----------------------------------------------------------------- *)
Section Generic.

Variable u : C.
Hypothesis Hu : Cadd C1 (Cadd u (Cmul u u)) = C0.

Lemma u_sq : Cmul u u = Copp (Cadd C1 u).
Proof.
  assert (E : Cmul u u
              = Cminus (Cadd C1 (Cadd u (Cmul u u))) (Cadd C1 u)) by ring.
  rewrite E, Hu. ring.
Qed.

Lemma u_sum : Cadd u (Cmul u u) = Copp C1.
Proof.
  assert (E : Cadd u (Cmul u u)
              = Cminus (Cadd C1 (Cadd u (Cmul u u))) C1) by ring.
  rewrite E, Hu. ring.
Qed.

(* u^3 = 1, because u^3 - 1 = (u-1)(1+u+u^2) and the second factor vanishes *)
Lemma u_cube : Cmul u (Cmul u u) = C1.
Proof.
  assert (E : Cminus (Cmul u (Cmul u u)) C1
              = Cmul (Cminus u C1) (Cadd C1 (Cadd u (Cmul u u)))) by ring.
  rewrite Hu in E.
  assert (E2 : Cmul (Cminus u C1) C0 = C0) by ring.
  rewrite E2 in E.
  assert (E3 : Cmul u (Cmul u u)
               = Cadd (Cminus (Cmul u (Cmul u u)) C1) C1) by ring.
  rewrite E3, E. ring.
Qed.

Lemma u_four : Cmul u (Cmul u (Cmul u u)) = u.
Proof. rewrite u_cube. ring. Qed.

(* the quadratic cofactor of the cubic factorization *)
Lemma quad_factor_gen : forall a b c : C,
  Cmul (Cadd a (Cadd (Cmul u b) (Cmul (Cmul u u) c)))
       (Cadd a (Cadd (Cmul (Cmul u u) b) (Cmul u c)))
  = Cminus (Cadd (Cmul a a) (Cadd (Cmul b b) (Cmul c c)))
           (Cadd (Cmul a b) (Cadd (Cmul b c) (Cmul c a))).
Proof.
  intros a b c.
  (* expand, keeping u^3 and u^4 as explicit products *)
  assert (E : Cmul (Cadd a (Cadd (Cmul u b) (Cmul (Cmul u u) c)))
                   (Cadd a (Cadd (Cmul (Cmul u u) b) (Cmul u c)))
              = Cadd (Cmul a a)
                (Cadd (Cmul (Cmul u (Cmul u u)) (Cmul b b))
                (Cadd (Cmul (Cmul u (Cmul u u)) (Cmul c c))
                (Cadd (Cmul (Cadd u (Cmul u u)) (Cmul a b))
                (Cadd (Cmul (Cadd u (Cmul u u)) (Cmul a c))
                      (Cmul (Cadd (Cmul u u) (Cmul u (Cmul u (Cmul u u))))
                            (Cmul b c))))))) by ring.
  (* rewrite u^4 BEFORE u^3: u^3 occurs inside u^4 *)
  rewrite E, u_four, u_cube.
  assert (Hbc : Cadd (Cmul u u) u = Copp C1) by (rewrite u_sq; ring).
  rewrite u_sum, Hbc. ring.
Qed.

(* the Z[omega] norm form *)
Lemma eisenstein_norm_gen : forall a b : C,
  Cmul (Cadd a (Cmul u b)) (Cadd a (Cmul (Cmul u u) b))
  = Cadd (Cminus (Cmul a a) (Cmul a b)) (Cmul b b).
Proof.
  intros a b.
  assert (E : Cmul (Cadd a (Cmul u b)) (Cadd a (Cmul (Cmul u u) b))
              = Cadd (Cmul a a)
                (Cadd (Cmul (Cadd u (Cmul u u)) (Cmul a b))
                      (Cmul (Cmul u (Cmul u u)) (Cmul b b)))) by ring.
  rewrite E, u_cube, u_sum. ring.
Qed.

End Generic.

(* ----------------------------------------------------------------- *)
(*  C.  the cubic factorization                                        *)
(* ----------------------------------------------------------------- *)
Lemma cube_sum_quad : forall a b c : C,
  Cminus (Cadd (Cpow a 3) (Cadd (Cpow b 3) (Cpow c 3)))
         (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul a (Cmul b c)))
  = Cmul (Cadd a (Cadd b c))
         (Cminus (Cadd (Cmul a a) (Cadd (Cmul b b) (Cmul c c)))
                 (Cadd (Cmul a b) (Cadd (Cmul b c) (Cmul c a)))).
Proof. intros a b c. cbn [Cpow]. ring. Qed.

Theorem cube_omega_factor : forall a b c : C,
  Cminus (Cadd (Cpow a 3) (Cadd (Cpow b 3) (Cpow c 3)))
         (Cmul (Cadd C1 (Cadd C1 C1)) (Cmul a (Cmul b c)))
  = Cmul (Cadd a (Cadd b c))
         (Cmul (Cadd a (Cadd (Cmul om b) (Cmul (Cmul om om) c)))
               (Cadd a (Cadd (Cmul (Cmul om om) b) (Cmul om c)))).
Proof.
  intros a b c.
  rewrite (quad_factor_gen om om_one_plus a b c).
  apply cube_sum_quad.
Qed.

(* the Eisenstein norm, at the actual cube root *)
Corollary eisenstein_norm_om : forall a b : C,
  Cmul (Cadd a (Cmul om b)) (Cadd a (Cmul (Cmul om om) b))
  = Cadd (Cminus (Cmul a a) (Cmul a b)) (Cmul b b).
Proof. exact (eisenstein_norm_gen om om_one_plus). Qed.

Print Assumptions om_one_plus.
Print Assumptions cube_omega_factor.
Print Assumptions eisenstein_norm_om.
