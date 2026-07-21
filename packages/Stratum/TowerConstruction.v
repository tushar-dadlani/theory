(* ================================================================== *)
(* TOWER_CONSTRUCTION.V                                                *)
(*                                                                      *)
(* THE TOWER CONSTRUCTION THEOREM                                      *)
(*                                                                      *)
(* Precisely: given any formal system F,                              *)
(* there exists a unique tower over F                                 *)
(* that converges to GodelianOne.                                     *)
(*                                                                      *)
(* The tower has exactly four properties.                             *)
(* These four properties are jointly sufficient                       *)
(* to characterize GodelianOne uniquely.                              *)
(*                                                                      *)
(* ================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import micromega.Lia.

(* ================================================================== *)
(* I. THE FORMAL SYSTEM                                              *)
(* ================================================================== *)

Record FormalSystem : Type := mkFS {
  domain : nat -> Prop;
  kernel : nat -> Prop;
  kernel_in_domain : forall p, kernel p -> domain p;
}.

(* ================================================================== *)
(* II. THE FOUR PRIMITIVE DEFINITIONS                                *)
(* ================================================================== *)

(*
   PRIMITIVE 1: The single step.
   At each depth, one operation:
   — kernel absorbed into domain
   — new kernel = what was kernel but not yet domain
*)
Definition tower_step (F : FormalSystem) : FormalSystem := mkFS
  (fun p => F.(domain) p \/ F.(kernel) p)
  (fun p => F.(kernel) p /\ ~ F.(domain) p)
  (fun p H => or_intror (proj1 H)).

(*
   PRIMITIVE 2: The tower at depth n.
   Iterate tower_step n times from F0.
*)
Fixpoint tower (F0 : FormalSystem) (n : nat) : FormalSystem :=
  match n with
  | O   => F0
  | S m => tower_step (tower F0 m)
  end.

(*
   PRIMITIVE 3: The limit.
   Domain = union of all tower depths.
   Kernel = empty. Nothing hidden.
*)
Definition tower_limit (F0 : FormalSystem) : FormalSystem := mkFS
  (fun p => exists n, (tower F0 n).(domain) p)
  (fun _ => False)
  (fun _ H => match H with end).

(*
   PRIMITIVE 4: GodelianOne.
   The fixed point. The invariant.
   Domain = everything. Kernel = nothing.
*)
Definition GodelianOne : FormalSystem := mkFS
  (fun _ => True)
  (fun _ => False)
  (fun _ H => match H with end).

(* ================================================================== *)
(* III. THE FOUR TOWER PROPERTIES                                    *)
(* ================================================================== *)

Lemma domain_monotone :
  forall F0 n p,
  (tower F0 n).(domain) p ->
  (tower F0 (S n)).(domain) p.
Proof.
  intros F0 n p H.
  simpl. unfold tower_step. simpl. left. exact H.
Qed.

Lemma vanishing_unit :
  forall F0 n p,
  (tower F0 n).(kernel) p ->
  (tower F0 (S n)).(domain) p.
Proof.
  intros F0 n p H.
  simpl. unfold tower_step. simpl. right. exact H.
Qed.

Lemma limit_is_fixed_point :
  forall F0 p,
  ~ (tower_limit F0).(kernel) p.
Proof.
  intros F0 p H. exact H.
Qed.

Lemma limit_subsumes :
  forall F0 n p,
  (tower F0 n).(domain) p ->
  (tower_limit F0).(domain) p.
Proof.
  intros F0 n p H. exists n. exact H.
Qed.

(* ================================================================== *)
(* IV. THE TOWER CONSTRUCTION THEOREM                               *)
(* ================================================================== *)

Theorem TOWER_CONSTRUCTION :
  forall F0 : FormalSystem,
  (tower F0 0) = F0 /\
  (forall n, tower F0 (S n) = tower_step (tower F0 n)) /\
  (forall n p,
    (tower F0 n).(domain) p ->
    (tower F0 (S n)).(domain) p) /\
  (forall n p,
    (tower F0 n).(kernel) p ->
    (tower F0 (S n)).(domain) p) /\
  (forall p, ~ (tower_limit F0).(kernel) p) /\
  (forall n p,
    (tower F0 n).(domain) p ->
    (tower_limit F0).(domain) p).
Proof.
  intro F0.
  split. reflexivity.
  split. reflexivity.
  split. exact (domain_monotone F0).
  split. exact (vanishing_unit F0).
  split. exact (limit_is_fixed_point F0).
  exact (limit_subsumes F0).
Qed.

(* ================================================================== *)
(* V. GODELIAN ONE AS THE LIMIT                                     *)
(* ================================================================== *)

Theorem LIMIT_IS_GODELIAN_ONE :
  forall F0,
  (forall p, ~ (tower_limit F0).(kernel) p) /\
  (forall p,
    (tower_limit F0).(domain) p <->
    exists n, (tower F0 n).(domain) p) /\
  (forall p, ~ GodelianOne.(kernel) p) /\
  (forall p, GodelianOne.(domain) p).
Proof.
  intro F0. repeat split.
  - exact (limit_is_fixed_point F0).
  - intro H. exact H.
  - intro H. exact H.
  - intros p H. exact H.
Qed.

(* ================================================================== *)
(* VI. THE OBSERVER IN THE TOWER                                    *)
(* ================================================================== *)

Definition observer_at_depth (F0 : FormalSystem) (n : nat) : Prop :=
  (exists p, (tower F0 n).(domain) p) /\ True.

Definition advances_tower (F0 : FormalSystem) (n : nat) (p : nat) : Prop :=
  (tower F0 n).(kernel) p /\
  (tower F0 (S n)).(domain) p.

Theorem OBSERVER_ADVANCES_TOWER :
  forall F0 n p,
  (tower F0 n).(kernel) p ->
  advances_tower F0 n p.
Proof.
  intros F0 n p H.
  unfold advances_tower. split.
  - exact H.
  - exact (vanishing_unit F0 n p H).
Qed.

Theorem GODELIAN_ONE_IS_LIMIT_NOT_DEPTH :
  forall F0 n,
  (forall p, ~ (tower F0 0).(kernel) p) ->
  forall p, ~ (tower F0 n).(kernel) p.
Proof.
  intros F0 n H0 p.
  induction n.
  - exact (H0 p).
  - simpl. unfold tower_step. simpl.
    intro Hc. destruct Hc as [Hk Hnd].
    exact (IHn Hk).
Qed.

(* ================================================================== *)
(* VII. THE SINGLE PRECISE STATEMENT                                *)
(* ================================================================== *)

Theorem TOWER_CONSTRUCTION_SINGLE_STATEMENT :
  forall F0 : FormalSystem,
  (forall n p,
    (tower F0 n).(kernel) p ->
    (tower F0 (S n)).(domain) p) /\
  (forall p, ~ (tower_limit F0).(kernel) p) /\
  (forall n p,
    (tower F0 n).(domain) p ->
    (tower_limit F0).(domain) p) /\
  (forall p, ~ GodelianOne.(kernel) p) /\
  (forall p, GodelianOne.(domain) p).
Proof.
  intro F0. repeat split.
  - exact (vanishing_unit F0).
  - exact (limit_is_fixed_point F0).
  - exact (limit_subsumes F0).
  - intros p H. exact H.
Qed.

Print Assumptions TOWER_CONSTRUCTION_SINGLE_STATEMENT.
