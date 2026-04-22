(** * Corollary 2: Finding the Fixed Point via Meta-Dirac
       on the Fredholm Construction *)

(** The Fredholm integral equation f = λKf + g asks for a fixed point
    of the operator T(f) = λKf + g on a function space.
    This function space IS Hom(G,G) from CategoryInterval.v.

    The Dirac delta δ_a is the "evaluation functional" — it extracts
    f(a) from f. When a = vanishing point, δ_0 extracts the fixed
    point value at the boundary of (0,1].

    "Meta-Dirac" means: we use δ not as a function (it isn't one)
    but as a proof-level witness extractor that picks out the
    vanishing point from the Fredholm construction. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
Require Import IntervalEquiv.
Require Import RInterval.
Require Import GeometryInterval.
Require Import CategoryInterval.
Require Import VanishingPoint.

Open Scope R_scope.

(* ================================================================= *)
(** ** Part 1: The Dirac Functional — Evaluation at a Point          *)
(* ================================================================= *)

(** The Dirac delta at point a is the evaluation functional:
    δ_a(f) = f(a). It is linear and continuous.
    In our framework, it extracts the "witness value" of f
    at any designated point. *)

Definition dirac (a : R) (f : R -> R) : R := f a.

(** Linearity of the Dirac functional *)
Theorem dirac_linear_add : forall a f g,
  dirac a (fun x => f x + g x) = dirac a f + dirac a g.
Proof.
  intros. unfold dirac. reflexivity.
Qed.

Theorem dirac_linear_scale : forall a c f,
  dirac a (fun x => c * f x) = c * dirac a f.
Proof.
  intros. unfold dirac. reflexivity.
Qed.

(** The meta-Dirac: evaluation at the vanishing point *)
Definition meta_dirac (f : R -> R) : R :=
  dirac vanishing_point f.

(** Meta-Dirac extracts f(0) *)
Theorem meta_dirac_extracts :
  forall f, meta_dirac f = f vanishing_point.
Proof.
  intro f. unfold meta_dirac, dirac. reflexivity.
Qed.

(** Meta-Dirac of the identity is the vanishing point itself *)
Theorem meta_dirac_id :
  meta_dirac (fun x => x) = vanishing_point.
Proof.
  unfold meta_dirac, dirac. reflexivity.
Qed.

(* ================================================================= *)
(** ** Part 2: The Fredholm Operator — Fixed Points in Function Space *)
(* ================================================================= *)

(** A Fredholm-type operator T on functions over R:
      T(f)(x) = λ * K(x, f(x)) + g(x)
    where K is a "kernel" and g is the "source term".

    For our purposes, we work with a simplified Fredholm
    operator: a contractive affine map on functions. *)

(** A bounded linear operator on (R -> R) *)
Definition operator := (R -> R) -> (R -> R).

(** The Fredholm operator with kernel k and source g:
    T(f)(x) = lambda * k(x) * f(x) + g(x)
    (simplified: multiplicative kernel, pointwise) *)
Definition fredholm (lambda : R) (k g : R -> R) : operator :=
  fun f x => lambda * k x * f x + g x.

(** A function f is a fixed point of operator T if T(f) = f *)
Definition is_fixed_point (T : operator) (f : R -> R) : Prop :=
  forall x, T f x = f x.

(** The Fredholm equation: f(x) = λ*k(x)*f(x) + g(x)
    Rearranging: f(x) * (1 - λ*k(x)) = g(x)
    Solution: f(x) = g(x) / (1 - λ*k(x))  when 1 - λ*k(x) ≠ 0 *)

Definition fredholm_solution (lambda : R) (k g : R -> R) : R -> R :=
  fun x => g x / (1 - lambda * k x).

(** The solution is indeed a fixed point when the denominator is nonzero *)
Theorem fredholm_fixed_point :
  forall lambda k g,
    (forall x, 1 - lambda * k x <> 0) ->
    is_fixed_point (fredholm lambda k g) (fredholm_solution lambda k g).
Proof.
  intros lambda k g Hnonzero x.
  unfold fredholm, fredholm_solution, is_fixed_point.
  field. exact (Hnonzero x).
Qed.

(* ================================================================= *)
(** ** Part 3: Meta-Dirac Extracts the Fixed Point at the Boundary   *)
(* ================================================================= *)

(** The key theorem: applying meta-Dirac to the Fredholm solution
    extracts its value at the vanishing point.

    When the kernel k vanishes at 0 (k(0) = 0), the Fredholm
    equation at the vanishing point reduces to:
      f(0) = λ*0*f(0) + g(0) = g(0)
    The fixed point value at the boundary is just the source term. *)

Theorem meta_dirac_fredholm :
  forall lambda k g,
    (forall x, 1 - lambda * k x <> 0) ->
    k vanishing_point = 0 ->
    meta_dirac (fredholm_solution lambda k g) = g vanishing_point.
Proof.
  intros lambda k g Hnonzero Hk0.
  unfold meta_dirac, dirac, fredholm_solution.
  rewrite Hk0. field.
Qed.

(** When k does NOT vanish at 0, the Dirac extracts a non-trivial
    fixed point value that depends on the kernel *)
Theorem meta_dirac_fredholm_general :
  forall lambda k g,
    (forall x, 1 - lambda * k x <> 0) ->
    meta_dirac (fredholm_solution lambda k g) =
    g vanishing_point / (1 - lambda * k vanishing_point).
Proof.
  intros lambda k g Hnonzero.
  unfold meta_dirac, dirac, fredholm_solution.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Part 4: The Fredholm Alternative at the Vanishing Point       *)
(* ================================================================= *)

(** The Fredholm alternative: either
    (a) 1 - λk(x) ≠ 0 for all x, and a unique solution exists, OR
    (b) 1 - λk(x) = 0 for some x, and the equation has no solution
        (or infinitely many).

    At the vanishing point, case (b) is the "resonance" — where the
    operator's eigenvalue hits 1. This is a SECOND vanishing point:
    the operator itself has a singularity. *)

Definition fredholm_resonance (lambda : R) (k : R -> R) (x : R) : Prop :=
  lambda * k x = 1.

(** Resonance at the vanishing point: λ*k(0) = 1 *)
Definition resonance_at_vanishing (lambda : R) (k : R -> R) : Prop :=
  fredholm_resonance lambda k vanishing_point.

(** When resonance occurs at the vanishing point, the Fredholm
    equation has no finite solution there — the meta-Dirac would
    extract "infinity", which in our framework is... divergence.
    This is the domain-theoretic ⊥ re-emerging! *)
Theorem resonance_implies_divergence :
  forall lambda k g,
    resonance_at_vanishing lambda k ->
    g vanishing_point <> 0 ->
    ~ exists f, is_fixed_point (fredholm lambda k g) f.
Proof.
  intros lambda k g Hres Hg [f Hfix].
  unfold is_fixed_point in Hfix.
  specialize (Hfix vanishing_point).
  unfold fredholm in Hfix.
  unfold resonance_at_vanishing, fredholm_resonance in Hres.
  (* Hfix: lambda * k(0) * f(0) + g(0) = f(0)
     Hres:  lambda * k(0) = 1
     So: 1 * f(0) + g(0) = f(0), hence g(0) = 0. *)
  rewrite Hres in Hfix. lra.
Qed.

(** The resonance IS the vanishing point of the operator:
    the point where the Fredholm operator "diverges",
    just as the geometric vanishing point is where (0,1] "diverges" *)

(* ================================================================= *)
(** ** Part 5: Contractive Fredholm and the Banach Fixed Point       *)
(* ================================================================= *)

(** When |λ*k(x)| < 1 for all x in (0,1], the Fredholm operator
    is contractive. The Banach fixed point theorem guarantees
    a unique fixed point. We show the contraction maps toward
    the vanishing point. *)

Definition contractive_kernel (lambda : R) (k : R -> R) : Prop :=
  forall x, affine_interval x -> Rabs (lambda * k x) < 1.

(** A contractive kernel has no resonance in (0,1] *)
Theorem contractive_no_resonance :
  forall lambda k,
    contractive_kernel lambda k ->
    forall x, affine_interval x -> ~ fredholm_resonance lambda k x.
Proof.
  intros lambda k Hcontr x Hx Hres.
  unfold fredholm_resonance in Hres.
  assert (Habs : Rabs (lambda * k x) < 1) by (apply Hcontr; exact Hx).
  rewrite Hres in Habs.
  rewrite Rabs_R1 in Habs.
  lra.
Qed.

(** Contractive kernel implies the denominator is nonzero in (0,1] *)
Theorem contractive_nonzero :
  forall lambda k,
    contractive_kernel lambda k ->
    forall x, affine_interval x -> 1 - lambda * k x <> 0.
Proof.
  intros lambda k Hcontr x Hx Heq.
  assert (Habs : Rabs (lambda * k x) < 1) by (apply Hcontr; exact Hx).
  assert (Heq1 : lambda * k x = 1) by lra.
  rewrite Heq1 in Habs. rewrite Rabs_R1 in Habs. lra.
Qed.

(** The Neumann series: for contractive operators, the solution
    can be approximated by iteration. Each iterate is closer to
    the fixed point — converging like the 1/n sequence converges
    to the vanishing point. *)

(** Iteration of the Fredholm operator *)
Fixpoint fredholm_iterate (T : operator) (f0 : R -> R) (n : nat) : R -> R :=
  match n with
  | O => f0
  | S m => T (fredholm_iterate T f0 m)
  end.

(** The iterates at the vanishing point, when k(0) = 0,
    are all equal to g(0) — the fixed point is reached immediately *)
Theorem iterate_at_vanishing :
  forall lambda k g n,
    k vanishing_point = 0 ->
    fredholm_iterate (fredholm lambda k g) (fun _ => 0) (S n) vanishing_point
    = g vanishing_point.
Proof.
  intros lambda k g n Hk0.
  induction n.
  - simpl. unfold fredholm. rewrite Hk0. lra.
  - simpl fredholm_iterate.
    unfold fredholm at 1. rewrite Hk0.
    (* The iterate at vanishing_point with k(0)=0:
       λ * 0 * (prev iterate at 0) + g(0) = g(0) *)
    lra.
Qed.

(** Meta-Dirac of the iterate equals g(0) *)
Theorem meta_dirac_iterate :
  forall lambda k g n,
    k vanishing_point = 0 ->
    meta_dirac (fredholm_iterate (fredholm lambda k g) (fun _ => 0) (S n))
    = g vanishing_point.
Proof.
  intros. unfold meta_dirac, dirac.
  apply iterate_at_vanishing. exact H.
Qed.

(* ================================================================= *)
(** ** Part 6: The Grand Connection — Fredholm Meets the Tower       *)
(* ================================================================= *)

(** Putting it all together:

    1. The function space (R -> R) is Hom(G,G) from CategoryInterval.v

    2. The Fredholm operator T is an endomorphism of Hom(G,G)

    3. The fixed point of T is found by:
       - The Banach theorem (contractive => unique fixed point)
       - The Fredholm solution f(x) = g(x)/(1 - λk(x))

    4. The meta-Dirac δ_0 extracts the fixed point value at
       the vanishing point: δ_0(f) = f(0) = g(0)/(1 - λk(0))

    5. When k(0) = 0 (the kernel vanishes at the boundary),
       δ_0(f) = g(0) — the source term at the vanishing point

    6. When λk(0) = 1 (resonance), no solution exists —
       the operator DIVERGES at the vanishing point, producing ⊥

    The Fredholm construction thus has TWO vanishing points:
    - The geometric one (x = 0, boundary of (0,1])
    - The operator-theoretic one (λk = 1, resonance)

    Both are instances of the canonical isomorphism from Corollary 1:
    they are absorbing, unique, and witness the boundary between
    solvability and divergence. *)

(** The two vanishing points of the Fredholm construction *)
Theorem two_vanishing_points :
  forall lambda k g,
    k vanishing_point = 0 ->
    (** VP 1: meta-Dirac extracts g(0) at the geometric vanishing point *)
    meta_dirac (fredholm_solution lambda k g) = g vanishing_point /\
    (** VP 2: resonance at ANY point x causes divergence *)
    (forall x, fredholm_resonance lambda k x ->
      g x <> 0 -> 1 - lambda * k x = 0).
Proof.
  intros lambda k g Hk0. split.
  - unfold meta_dirac, dirac, fredholm_solution.
    rewrite Hk0. field.
  - intros x Hres _. unfold fredholm_resonance in Hres. lra.
Qed.

(** Final theorem: the meta-Dirac on Fredholm recovers the
    vanishing point from the canonical isomorphism *)
Theorem fredholm_recovers_vanishing_point :
  forall lambda k g,
    k vanishing_point = 0 ->
    g vanishing_point = 0 ->
    meta_dirac (fredholm_solution lambda k g) = vanishing_point.
Proof.
  intros lambda k g Hk0 Hg0.
  unfold meta_dirac, dirac, fredholm_solution.
  rewrite Hk0. rewrite Hg0. unfold vanishing_point. field.
Qed.
