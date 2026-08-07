(* ================================================================= *)
(*  CPathIntegral.v  —  Milestone C, brick C1b: parametrized path       *)
(*  (contour) integrals of a C-valued function.                        *)
(*                                                                    *)
(*  pathint gam gam' f Hf a b = ∫_a^b f(gam u)·gam'(u) du  (Cintf of the *)
(*  integrand).  Provides path concatenation (from Cintf_additive), the *)
(*  ML/length estimate, and the two concrete Newman contour pieces:     *)
(*  the straight SEGMENT and the circular ARC (centre 0, radius R), with *)
(*  their derivatives gam', component continuity, and |gam'| facts.     *)
(*  The path FTC (primitive ⇒ pathint = H(end)−H(start)) is C1c.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2.
Open Scope R_scope.

(* ---- the path integral ---- *)
Definition pathint (gam gam' : R -> C) (f : C -> C)
  (Hf : Ccont (fun u => Cmul (f (gam u)) (gam' u))) (a b : R) : C :=
  Cintf (fun u => Cmul (f (gam u)) (gam' u)) Hf a b.

(* ---- concatenation of paths (split the parameter interval) ---- *)
Lemma pathint_split : forall gam gam' f Hf a b c,
  pathint gam gam' f Hf a c
  = Cadd (pathint gam gam' f Hf a b) (pathint gam gam' f Hf b c).
Proof. intros; unfold pathint; apply Cintf_additive. Qed.

Lemma pathint_swap : forall gam gam' f Hf a b,
  pathint gam gam' f Hf b a = Copp (pathint gam gam' f Hf a b).
Proof. intros; unfold pathint; apply Cintf_swap. Qed.

(* ---- the ML (length) estimate ---- *)
Lemma pathint_ML : forall gam gam' f Hf a b M, a <= b ->
  (forall u, a <= u <= b -> Cmod (Cmul (f (gam u)) (gam' u)) <= M) ->
  Cmod (pathint gam gam' f Hf a b) <= 2 * M * (b - a).
Proof. intros; unfold pathint; apply Cintf_ML; assumption. Qed.

(* ================================================================= *)
(*  The concrete Newman contour pieces.                                *)
(* ================================================================= *)

(* ---- the straight segment from z0 to z1: gam u = z0 + u(z1−z0) ---- *)
Definition seg (z0 z1 : C) (u : R) : C := Cadd z0 (Cmul (RtoC u) (Cminus z1 z0)).
Definition seg' (z0 z1 : C) (u : R) : C := Cminus z1 z0.

Lemma seg_0 : forall z0 z1, seg z0 z1 0 = z0.
Proof. intros z0 z1; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.

Lemma seg_1 : forall z0 z1, seg z0 z1 1 = z1.
Proof. intros z0 z1; unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring. Qed.

Lemma Ccont_seg : forall z0 z1, Ccont (seg z0 z1).
Proof.
  intros z0 z1; split; intro x.
  - assert (Heq : (fun u => Re (seg z0 z1 u)) = (fun u => Re z0 + u * (Re z1 - Re z0)))
      by (apply functional_extensionality; intro u;
          unfold seg, Cadd, Cmul, RtoC, Cminus; cbn [Re Im]; ring).
    rewrite Heq; apply derivable_continuous_pt, derivable_pt_plus;
      [ apply derivable_pt_const
      | apply derivable_pt_mult; [ apply derivable_pt_id | apply derivable_pt_const ] ].
  - assert (Heq : (fun u => Im (seg z0 z1 u)) = (fun u => Im z0 + u * (Im z1 - Im z0)))
      by (apply functional_extensionality; intro u;
          unfold seg, Cadd, Cmul, RtoC, Cminus; cbn [Re Im]; ring).
    rewrite Heq; apply derivable_continuous_pt, derivable_pt_plus;
      [ apply derivable_pt_const
      | apply derivable_pt_mult; [ apply derivable_pt_id | apply derivable_pt_const ] ].
Qed.

Lemma Ccont_seg' : forall z0 z1, Ccont (seg' z0 z1).
Proof. intros z0 z1; apply Ccont_const. Qed.

(* ---- the circular arc, centre 0, radius R:  gam u = R(cos u, sin u) ---- *)
Definition arc (r : R) (u : R) : C := mkC (r * cos u) (r * sin u).
Definition arc' (r : R) (u : R) : C := mkC (- (r * sin u)) (r * cos u).

Lemma Cmod_arc : forall r u, 0 <= r -> Cmod (arc r u) = r.
Proof.
  intros r u Hr; unfold arc, Cmod, Cnorm2; cbn [Re Im].
  replace (r * cos u * (r * cos u) + r * sin u * (r * sin u))
    with (r * r * (cos u * cos u + sin u * sin u)) by ring.
  assert (Hp : cos u * cos u + sin u * sin u = 1)
    by (pose proof (sin2_cos2 u); unfold Rsqr in *; lra).
  rewrite Hp, Rmult_1_r; apply sqrt_square; exact Hr.
Qed.

Lemma Cmod_arc' : forall r u, 0 <= r -> Cmod (arc' r u) = r.
Proof.
  intros r u Hr; unfold arc', Cmod, Cnorm2; cbn [Re Im].
  replace (- (r * sin u) * - (r * sin u) + r * cos u * (r * cos u))
    with (r * r * (cos u * cos u + sin u * sin u)) by ring.
  assert (Hp : cos u * cos u + sin u * sin u = 1)
    by (pose proof (sin2_cos2 u); unfold Rsqr in *; lra).
  rewrite Hp, Rmult_1_r; apply sqrt_square; exact Hr.
Qed.

Lemma Ccont_arc : forall r, Ccont (arc r).
Proof.
  intro r; split; intro x; unfold arc; cbn [Re Im].
  - apply continuity_pt_mult;
      [ apply continuity_pt_const; intro; reflexivity | apply continuity_cos ].
  - apply continuity_pt_mult;
      [ apply continuity_pt_const; intro; reflexivity | apply continuity_sin ].
Qed.

Lemma Ccont_arc' : forall r, Ccont (arc' r).
Proof.
  intro r; split; intro x; unfold arc'; cbn [Re Im].
  - apply (continuity_pt_opp (fun u => r * sin u));
      apply continuity_pt_mult;
      [ apply continuity_pt_const; intro; reflexivity | apply continuity_sin ].
  - apply continuity_pt_mult;
      [ apply continuity_pt_const; intro; reflexivity | apply continuity_cos ].
Qed.

Print Assumptions pathint_ML.

(* ================================================================= *)
(*  END CPathIntegral.v  —  contour integrals + segment/arc pieces.     *)
(* ================================================================= *)
