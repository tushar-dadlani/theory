(* ================================================================= *)
(*  ARC2_FullHomomorphism.v                                           *)
(*                                                                    *)
(*  THE FULL I-AXIS-AWARE HOMOMORPHISM THEOREM                        *)
(*                                                                    *)
(*  STATEMENT (universal, nat level):                                 *)
(*    For ANY tasks A, B and ANY test grid that doesn't trigger an  *)
(*    I-axis lookup match in (A ++ B), or in A after applying B's   *)
(*    N-axis transform, the full nat solver factors as a monoid     *)
(*    homomorphism:                                                    *)
(*      kleisli_full (A ++ B) test =                                 *)
(*      kleisli_full A (kleisli_full B test)                          *)
(*    (assuming the third demo_lookup is also None — this gives the *)
(*    pure homomorphism form via two compositions of kleisli_full.)  *)
(*                                                                    *)
(*  PROOF STRATEGY:                                                   *)
(*    1. distributivity of serialize/transforms over ++              *)
(*    2. demo_lookup None on append iff None on both                 *)
(*    3. eval (compose_list (xs ++ ys)) factors semantically         *)
(*    4. n_axis_solver_nat is unconditionally homomorphic             *)
(*    5. kleisli_full = n_axis when no demo_lookup match              *)
(*    6. Combine via three no-lookup hypotheses                      *)
(*    7. Color level closed pointwise by reflexivity (sidestepping  *)
(*       the bind_solver round-trip)                                  *)
(*                                                                    *)
(*  EUCLIDEAN: the demo set is a finite set of "anchor" points on  *)
(*    the grid manifold. The full solver walks the geodesic UNLESS *)
(*    the test is at an anchor, in which case it teleports to the  *)
(*    cached destination. Off the anchor set, full = N-axis.        *)
(*                                                                    *)
(*  GAUSSIAN: the N-axis is a clean group homomorphism into Aut(    *)
(*    Grid). The full solver is a localization at the demo set —   *)
(*    formally, a quotient by "test = gi → answer = go" for each   *)
(*    (gi, go) in demos. The localization is finite, decidable,    *)
(*    and the decidable check is captured in demo_lookup_misses.   *)
(*                                                                    *)
(*  Uses functional_extensionality for ONE function-level identity. *)
(*  ZERO Admitted.                                                    *)
(* ================================================================= *)

From Coq Require Import Arith Lia PeanoNat Lists.List Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(* PART 0 — REIMPORTED PRIMITIVES                                     *)
(* ================================================================= *)

Inductive Color10 : Type :=
  | C0  : Color10 | C1  : Color10 | C2  : Color10 | C3  : Color10
  | C4  : Color10 | C5  : Color10 | C6  : Color10 | C7  : Color10
  | C8  : Color10 | C9  : Color10.

Definition color_to_nat (c : Color10) : nat :=
  match c with
  | C0 => 0 | C1 => 1 | C2 => 2 | C3 => 3 | C4 => 4
  | C5 => 5 | C6 => 6 | C7 => 7 | C8 => 8 | C9 => 9
  end.

Definition nat_to_color (n : nat) : option Color10 :=
  match n with
  | 0 => Some C0 | 1 => Some C1 | 2 => Some C2 | 3 => Some C3
  | 4 => Some C4 | 5 => Some C5 | 6 => Some C6 | 7 => Some C7
  | 8 => Some C8 | 9 => Some C9
  | _ => None
  end.

Definition nat_to_color_total (n : nat) : Color10 :=
  match nat_to_color n with
  | Some c => c
  | None   => C0
  end.

Definition CGrid := list (list Color10).
Definition Demo  := (CGrid * CGrid)%type.
Definition Demos := list Demo.
Definition Grid := list (list nat).
Definition NatDemo := (Grid * Grid)%type.

Definition serialize_row (cs : list Color10) : list nat := map color_to_nat cs.
Definition serialize_grid (g : CGrid) : Grid := map serialize_row g.
Definition serialize_demo (d : Demo) : NatDemo :=
  let (gi, go) := d in (serialize_grid gi, serialize_grid go).
Definition serialize_demos (ds : Demos) : list NatDemo := map serialize_demo ds.
Definition deserialize_row (xs : list nat) : list Color10 := map nat_to_color_total xs.
Definition deserialize_grid (g : Grid) : CGrid := map deserialize_row g.

(* ================================================================= *)
(* PART 1 — GRID PRIMITIVES                                           *)
(* ================================================================= *)

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint grid_eqb (g1 g2 : Grid) : bool :=
  match g1, g2 with
  | [], [] => true
  | r1 :: rs1, r2 :: rs2 => nat_list_eqb r1 r2 && grid_eqb rs1 rs2
  | _, _ => false
  end.

Definition flip_h (g : Grid) : Grid := map (@rev nat) g.
Definition flip_v (g : Grid) : Grid := @rev (list nat) g.

Fixpoint heads (g : Grid) : list nat :=
  match g with [] => [] | [] :: rs => heads rs | (c :: _) :: rs => c :: heads rs end.
Fixpoint tails (g : Grid) : Grid :=
  match g with [] => [] | [] :: rs => tails rs | (_ :: r) :: rs => r :: tails rs end.
Definition grid_cols (g : Grid) : nat :=
  match g with [] => 0 | r :: _ => length r end.

Fixpoint transpose_aux (fuel : nat) (g : Grid) : Grid :=
  match fuel with
  | 0 => []
  | S k =>
      match g with
      | [] => []
      | _ =>
          let h := heads g in
          if Nat.eqb (length h) 0 then []
          else h :: transpose_aux k (tails g)
      end
  end.

Definition transpose (g : Grid) : Grid := transpose_aux (grid_cols g) g.
Definition rotate_180 (g : Grid) : Grid := flip_v (flip_h g).

(* ================================================================= *)
(* PART 2 — TRANSFORM AST                                             *)
(* ================================================================= *)

Inductive Transform : Type :=
  | TF_Identity   : Transform
  | TF_FlipH      : Transform
  | TF_FlipV      : Transform
  | TF_Rotate180  : Transform
  | TF_Transpose  : Transform
  | TF_Compose    : Transform -> Transform -> Transform.

Definition arc_compose (f g : Grid -> Grid) : Grid -> Grid := fun x => f (g x).

Fixpoint eval (t : Transform) : Grid -> Grid :=
  match t with
  | TF_Identity        => fun g => g
  | TF_FlipH           => flip_h
  | TF_FlipV           => flip_v
  | TF_Rotate180       => rotate_180
  | TF_Transpose       => transpose
  | TF_Compose t1 t2   => arc_compose (eval t1) (eval t2)
  end.

Definition demo_to_transform (g_in g_out : Grid) : Transform :=
  if grid_eqb g_in g_out                     then TF_Identity
  else if grid_eqb g_out (flip_h g_in)       then TF_FlipH
  else if grid_eqb g_out (flip_v g_in)       then TF_FlipV
  else if grid_eqb g_out (rotate_180 g_in)   then TF_Rotate180
  else if grid_eqb g_out (transpose g_in)    then TF_Transpose
  else TF_Identity.

Definition demos_to_transforms (demos : list NatDemo) : list Transform :=
  map (fun p => demo_to_transform (fst p) (snd p)) demos.

Fixpoint compose_list (ts : list Transform) : Transform :=
  match ts with
  | []        => TF_Identity
  | [t]       => t
  | t :: rest => TF_Compose t (compose_list rest)
  end.

Definition multi_demo_to_transform (demos : list NatDemo) : Transform :=
  compose_list (demos_to_transforms demos).

Fixpoint demo_lookup (xs : list NatDemo) (g : Grid) : option Grid :=
  match xs with
  | [] => None
  | (gi, go) :: rest =>
      if grid_eqb g gi then Some go else demo_lookup rest g
  end.

Definition kleisli_full (demos : list NatDemo) (test : Grid) : Grid :=
  match demo_lookup demos test with
  | Some go => go
  | None    => eval (multi_demo_to_transform demos) test
  end.

Definition Solver : Type := Demos -> CGrid -> CGrid.

Definition bind_solver (ns : list NatDemo -> Grid -> Grid) : Solver :=
  fun demos test =>
    deserialize_grid (ns (serialize_demos demos) (serialize_grid test)).

Definition kleisli_color_full : Solver := bind_solver kleisli_full.

(* ================================================================= *)
(* PART 3 — TASK + CONCAT                                              *)
(* ================================================================= *)

Definition CTask : Type := Demos.
Definition idTask : CTask := [].

Definition task_morphism (T : CTask) : CGrid -> CGrid :=
  fun test => kleisli_color_full T test.

Definition task_concat (A B : CTask) : CTask := A ++ B.

Notation "A '+++' B" := (task_concat A B) (at level 60, right associativity).

Definition n_axis_solver_nat (demos : list NatDemo) (test : Grid) : Grid :=
  eval (multi_demo_to_transform demos) test.

(* ================================================================= *)
(* PART 4 — DISTRIBUTIVITY OVER list APPEND                            *)
(* ================================================================= *)

Lemma serialize_demos_app : forall A B,
  serialize_demos (A ++ B) = serialize_demos A ++ serialize_demos B.
Proof. intros. unfold serialize_demos. apply map_app. Qed.

Lemma demos_to_transforms_app : forall xs ys,
  demos_to_transforms (xs ++ ys) =
  demos_to_transforms xs ++ demos_to_transforms ys.
Proof. intros. unfold demos_to_transforms. apply map_app. Qed.

(* ================================================================= *)
(* PART 5 — demo_lookup BEHAVIOR ON APPEND                            *)
(* ================================================================= *)

Lemma demo_lookup_app_none_iff : forall xs ys g,
  demo_lookup (xs ++ ys) g = None <->
  demo_lookup xs g = None /\ demo_lookup ys g = None.
Proof.
  induction xs as [|d rest IH]; intros ys g.
  - simpl. split.
    + intro H. split; [reflexivity | exact H].
    + intros [_ H]. exact H.
  - simpl. destruct d as [gi go]. destruct (grid_eqb g gi) eqn:E.
    + split.
      * discriminate.
      * intros [H _]. discriminate H.
    + apply IH.
Qed.

Lemma demo_lookup_app_none_intro : forall xs ys g,
  demo_lookup xs g = None ->
  demo_lookup ys g = None ->
  demo_lookup (xs ++ ys) g = None.
Proof.
  intros xs ys g H1 H2.
  apply demo_lookup_app_none_iff. split; assumption.
Qed.

(* ================================================================= *)
(* PART 6 — eval (compose_list (xs ++ ys)) FACTORS SEMANTICALLY        *)
(* ================================================================= *)

Lemma eval_compose_list_app : forall xs ys g,
  eval (compose_list (xs ++ ys)) g =
  eval (compose_list xs) (eval (compose_list ys) g).
Proof.
  induction xs as [|t rest IH]; intros ys g.
  - simpl. reflexivity.
  - simpl.
    destruct (rest ++ ys) as [|h tl] eqn:E.
    + apply app_eq_nil in E. destruct E as [Erest Eys].
      subst rest. subst ys. simpl. reflexivity.
    + destruct rest as [|t2 rest'].
      * simpl in E. subst ys. simpl.
        destruct tl as [|h2 tl'].
        -- simpl. unfold arc_compose. reflexivity.
        -- simpl. unfold arc_compose. reflexivity.
      * simpl. unfold arc_compose. f_equal.
        simpl in E. inversion E. subst h. subst tl.
        change (t2 :: rest' ++ ys) with ((t2 :: rest') ++ ys).
        apply IH.
Qed.

(* ================================================================= *)
(* PART 7 — multi_demo_to_transform AND n_axis_solver_nat              *)
(* ================================================================= *)

Lemma eval_multi_demo_to_transform_app : forall xs ys g,
  eval (multi_demo_to_transform (xs ++ ys)) g =
  eval (multi_demo_to_transform xs) (eval (multi_demo_to_transform ys) g).
Proof.
  intros xs ys g. unfold multi_demo_to_transform.
  rewrite demos_to_transforms_app.
  apply eval_compose_list_app.
Qed.

Theorem n_axis_solver_homomorphism : forall xs ys test,
  n_axis_solver_nat (xs ++ ys) test =
  n_axis_solver_nat xs (n_axis_solver_nat ys test).
Proof.
  intros xs ys test. unfold n_axis_solver_nat.
  apply eval_multi_demo_to_transform_app.
Qed.

Theorem n_axis_solver_strict_homomorphism : forall xs ys,
  n_axis_solver_nat (xs ++ ys) =
  fun test => n_axis_solver_nat xs (n_axis_solver_nat ys test).
Proof.
  intros xs ys. apply functional_extensionality. intro test.
  apply n_axis_solver_homomorphism.
Qed.

(* ================================================================= *)
(* PART 8 — kleisli_full WITH NO LOOKUP REDUCES TO N-AXIS              *)
(* ================================================================= *)

Lemma kleisli_full_no_lookup : forall demos test,
  demo_lookup demos test = None ->
  kleisli_full demos test = n_axis_solver_nat demos test.
Proof.
  intros demos test H. unfold kleisli_full, n_axis_solver_nat.
  rewrite H. reflexivity.
Qed.

(* ================================================================= *)
(* PART 9 — THE MAIN THEOREM AT NAT LEVEL                              *)
(* ================================================================= *)

Theorem full_homomorphism_nat : forall xs ys test,
  demo_lookup (xs ++ ys) test = None ->
  demo_lookup xs (n_axis_solver_nat ys test) = None ->
  kleisli_full (xs ++ ys) test =
  kleisli_full xs (n_axis_solver_nat ys test).
Proof.
  intros xs ys test HconcatNone HafterBNone.
  rewrite kleisli_full_no_lookup by exact HconcatNone.
  rewrite n_axis_solver_homomorphism.
  rewrite kleisli_full_no_lookup by exact HafterBNone.
  reflexivity.
Qed.

(* The strict three-hypothesis version: when NONE of the three
   demo_lookups fire, kleisli_full factors as a clean homomorphism. *)
Theorem kleisli_full_factors : forall xs ys test,
  demo_lookup (xs ++ ys) test = None ->
  demo_lookup xs (n_axis_solver_nat ys test) = None ->
  demo_lookup ys test = None ->
  kleisli_full (xs ++ ys) test =
  kleisli_full xs (kleisli_full ys test).
Proof.
  intros xs ys test H1 H2 H3.
  rewrite (full_homomorphism_nat xs ys test H1 H2).
  rewrite <- (kleisli_full_no_lookup ys test H3).
  reflexivity.
Qed.

(* ================================================================= *)
(* PART 10 — VALUE PRESERVATION                                       *)
(* ================================================================= *)

Lemma serialize_deserialize_row_bounded : forall xs,
  Forall (fun n => n < 10) xs ->
  serialize_row (deserialize_row xs) = xs.
Proof.
  intros xs H.
  unfold serialize_row, deserialize_row.
  rewrite map_map.
  induction xs as [|x rest IH]; simpl.
  - reflexivity.
  - inversion H. subst.
    rewrite IH; [|exact H3].
    f_equal.
    unfold nat_to_color_total.
    repeat (destruct x as [|x]; [reflexivity|]).
    exfalso. lia.
Qed.

Lemma serialize_deserialize_grid_bounded : forall g,
  Forall (Forall (fun n => n < 10)) g ->
  serialize_grid (deserialize_grid g) = g.
Proof.
  intros g H. unfold serialize_grid, deserialize_grid.
  rewrite map_map.
  induction g as [|r rest IH]; simpl.
  - reflexivity.
  - inversion H. subst.
    rewrite IH by exact H3.
    rewrite serialize_deserialize_row_bounded by exact H2.
    reflexivity.
Qed.

Lemma deserialize_serialize_row : forall r,
  deserialize_row (serialize_row r) = r.
Proof.
  intro r. unfold deserialize_row, serialize_row.
  rewrite map_map.
  induction r as [|c rest IH]; simpl.
  - reflexivity.
  - destruct c; simpl; rewrite IH; reflexivity.
Qed.

Lemma deserialize_serialize_grid : forall g,
  deserialize_grid (serialize_grid g) = g.
Proof.
  intro g. unfold deserialize_grid, serialize_grid.
  rewrite map_map.
  induction g as [|r rest IH]; simpl.
  - reflexivity.
  - rewrite deserialize_serialize_row. f_equal. exact IH.
Qed.

(* ================================================================= *)
(* PART 11 — TASK MORPHISM AT idTask                                   *)
(* ================================================================= *)

Theorem task_morphism_id : forall g,
  task_morphism idTask g = g.
Proof.
  intro g. unfold task_morphism, kleisli_color_full, bind_solver,
                  kleisli_full, idTask.
  simpl. apply deserialize_serialize_grid.
Qed.

Theorem task_morphism_id_concat : forall A test,
  task_morphism (idTask +++ A) test = task_morphism A test.
Proof.
  intros A test. unfold task_concat, idTask. simpl. reflexivity.
Qed.

Theorem task_morphism_concat_id : forall A test,
  task_morphism (A +++ idTask) test = task_morphism A test.
Proof.
  intros A test. unfold task_concat, idTask. rewrite app_nil_r.
  reflexivity.
Qed.

(* ================================================================= *)
(* PART 12 — DECIDABLE NO-LOOKUP CHECK                                 *)
(* ================================================================= *)

Definition demo_lookup_misses (demos : list NatDemo) (g : Grid) : bool :=
  match demo_lookup demos g with
  | Some _ => false
  | None   => true
  end.

Lemma demo_lookup_misses_iff : forall demos g,
  demo_lookup_misses demos g = true <-> demo_lookup demos g = None.
Proof.
  intros demos g. unfold demo_lookup_misses.
  destruct (demo_lookup demos g); split; intro H;
    try reflexivity; try discriminate.
Qed.

(* ================================================================= *)
(* PART 13 — POINTWISE COLOR-LEVEL HOMOMORPHISM                        *)
(* ================================================================= *)

Definition flip_h_task : CTask :=
  [ ([[C1; C2; C3]; [C4; C5; C6]],
     [[C3; C2; C1]; [C6; C5; C4]]) ].

Definition flip_v_task : CTask :=
  [ ([[C1; C2]; [C3; C4]; [C5; C6]],
     [[C5; C6]; [C3; C4]; [C1; C2]]) ].

Definition transpose_task : CTask :=
  [ ([[C1; C2; C3]; [C4; C5; C6]],
     [[C1; C4]; [C2; C5]; [C3; C6]]) ].

Theorem color_homomorphism_flip_h_double :
  task_morphism (flip_h_task +++ flip_h_task) [[C7; C8]; [C9; C0]] =
  task_morphism flip_h_task
    (task_morphism flip_h_task [[C7; C8]; [C9; C0]]).
Proof. reflexivity. Qed.

Theorem color_homomorphism_flip_h_flip_v :
  task_morphism (flip_h_task +++ flip_v_task) [[C1; C2]; [C3; C4]] =
  task_morphism flip_h_task
    (task_morphism flip_v_task [[C1; C2]; [C3; C4]]).
Proof. reflexivity. Qed.

Theorem color_homomorphism_transpose_flip_h :
  task_morphism (transpose_task +++ flip_h_task) [[C1; C2]; [C3; C4]] =
  task_morphism transpose_task
    (task_morphism flip_h_task [[C1; C2]; [C3; C4]]).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 14 — CONCRETE NAT-LEVEL APPLICATIONS OF THE UNIVERSAL THEOREM *)
(* ================================================================= *)

Definition flip_h_demo_nat : NatDemo :=
  ([[1;2;3];[4;5;6]], [[3;2;1];[6;5;4]]).

Definition flip_v_demo_nat : NatDemo :=
  ([[1;2];[3;4];[5;6]], [[5;6];[3;4];[1;2]]).

Theorem nat_homomorphism_flip_h_double :
  kleisli_full ([flip_h_demo_nat] ++ [flip_h_demo_nat]) [[7;8];[9;0]] =
  kleisli_full [flip_h_demo_nat]
    (kleisli_full [flip_h_demo_nat] [[7;8];[9;0]]).
Proof.
  apply kleisli_full_factors; reflexivity.
Qed.

Theorem nat_homomorphism_flip_h_flip_v :
  kleisli_full ([flip_h_demo_nat] ++ [flip_v_demo_nat]) [[1;2];[3;4]] =
  kleisli_full [flip_h_demo_nat]
    (kleisli_full [flip_v_demo_nat] [[1;2];[3;4]]).
Proof.
  apply kleisli_full_factors; reflexivity.
Qed.

(* ================================================================= *)
(* PART 15 — THE MASTER THEOREM                                       *)
(* ================================================================= *)

Theorem FULL_HOMOMORPHISM_OK :
  (* (1) Distributivity laws. *)
  (forall A B, serialize_demos (A ++ B) =
               serialize_demos A ++ serialize_demos B) /\
  (forall xs ys, demos_to_transforms (xs ++ ys) =
                 demos_to_transforms xs ++ demos_to_transforms ys) /\
  (forall xs ys g,
    demo_lookup (xs ++ ys) g = None <->
    demo_lookup xs g = None /\ demo_lookup ys g = None) /\
  (* (2) Semantic distributivity of compose_list and multi_demo. *)
  (forall xs ys g,
    eval (compose_list (xs ++ ys)) g =
    eval (compose_list xs) (eval (compose_list ys) g)) /\
  (forall xs ys g,
    eval (multi_demo_to_transform (xs ++ ys)) g =
    eval (multi_demo_to_transform xs)
         (eval (multi_demo_to_transform ys) g)) /\
  (* (3) N-axis homomorphism — universal, unconditional, nat level. *)
  (forall xs ys test,
    n_axis_solver_nat (xs ++ ys) test =
    n_axis_solver_nat xs (n_axis_solver_nat ys test)) /\
  (* (4) N-axis as function-level identity (with funext). *)
  (forall xs ys,
    n_axis_solver_nat (xs ++ ys) =
    fun test => n_axis_solver_nat xs (n_axis_solver_nat ys test)) /\
  (* (5) kleisli_full reduces to n_axis when no lookup match. *)
  (forall demos test,
    demo_lookup demos test = None ->
    kleisli_full demos test = n_axis_solver_nat demos test) /\
  (* (6) THE MAIN UNIVERSAL THEOREM at nat level. *)
  (forall xs ys test,
    demo_lookup (xs ++ ys) test = None ->
    demo_lookup xs (n_axis_solver_nat ys test) = None ->
    kleisli_full (xs ++ ys) test =
    kleisli_full xs (n_axis_solver_nat ys test)) /\
  (* (7) Strengthened version with three hypotheses. *)
  (forall xs ys test,
    demo_lookup (xs ++ ys) test = None ->
    demo_lookup xs (n_axis_solver_nat ys test) = None ->
    demo_lookup ys test = None ->
    kleisli_full (xs ++ ys) test =
    kleisli_full xs (kleisli_full ys test)) /\
  (* (8) Value preservation lemmas. *)
  (forall xs,
    Forall (fun n => n < 10) xs ->
    serialize_row (deserialize_row xs) = xs) /\
  (forall g,
    Forall (Forall (fun n => n < 10)) g ->
    serialize_grid (deserialize_grid g) = g) /\
  (* (9) Round-trip lemmas. *)
  (forall r, deserialize_row (serialize_row r) = r) /\
  (forall g, deserialize_grid (serialize_grid g) = g) /\
  (* (10) idTask laws. *)
  (forall g, task_morphism idTask g = g) /\
  (forall A test, task_morphism (idTask +++ A) test = task_morphism A test) /\
  (forall A test, task_morphism (A +++ idTask) test = task_morphism A test) /\
  (* (11) Concrete color-level homomorphism instances. *)
  (task_morphism (flip_h_task +++ flip_h_task) [[C7; C8]; [C9; C0]] =
   task_morphism flip_h_task
     (task_morphism flip_h_task [[C7; C8]; [C9; C0]])) /\
  (task_morphism (flip_h_task +++ flip_v_task) [[C1; C2]; [C3; C4]] =
   task_morphism flip_h_task
     (task_morphism flip_v_task [[C1; C2]; [C3; C4]])) /\
  (task_morphism (transpose_task +++ flip_h_task) [[C1; C2]; [C3; C4]] =
   task_morphism transpose_task
     (task_morphism flip_h_task [[C1; C2]; [C3; C4]])) /\
  (* (12) Concrete nat-level applications of the universal theorem. *)
  (kleisli_full ([flip_h_demo_nat] ++ [flip_h_demo_nat]) [[7;8];[9;0]] =
   kleisli_full [flip_h_demo_nat]
     (kleisli_full [flip_h_demo_nat] [[7;8];[9;0]])) /\
  (kleisli_full ([flip_h_demo_nat] ++ [flip_v_demo_nat]) [[1;2];[3;4]] =
   kleisli_full [flip_h_demo_nat]
     (kleisli_full [flip_v_demo_nat] [[1;2];[3;4]])) /\
  (* (13) Decidable no-lookup check. *)
  (forall demos g,
    demo_lookup_misses demos g = true <-> demo_lookup demos g = None).
Proof.
  split. { exact serialize_demos_app. }
  split. { exact demos_to_transforms_app. }
  split. { exact demo_lookup_app_none_iff. }
  split. { exact eval_compose_list_app. }
  split. { exact eval_multi_demo_to_transform_app. }
  split. { exact n_axis_solver_homomorphism. }
  split. { exact n_axis_solver_strict_homomorphism. }
  split. { exact kleisli_full_no_lookup. }
  split. { exact full_homomorphism_nat. }
  split. { exact kleisli_full_factors. }
  split. { exact serialize_deserialize_row_bounded. }
  split. { exact serialize_deserialize_grid_bounded. }
  split. { exact deserialize_serialize_row. }
  split. { exact deserialize_serialize_grid. }
  split. { exact task_morphism_id. }
  split. { exact task_morphism_id_concat. }
  split. { exact task_morphism_concat_id. }
  split. { exact color_homomorphism_flip_h_double. }
  split. { exact color_homomorphism_flip_h_flip_v. }
  split. { exact color_homomorphism_transpose_flip_h. }
  split. { exact nat_homomorphism_flip_h_double. }
  split. { exact nat_homomorphism_flip_h_flip_v. }
  exact demo_lookup_misses_iff.
Qed.

Print Assumptions FULL_HOMOMORPHISM_OK.

(* ================================================================= *)
(*  QED.                                                              *)
(*                                                                    *)
(*  THE STRUCTURE THEOREM:                                            *)
(*                                                                    *)
(*  AT THE NAT LEVEL:                                                 *)
(*    n_axis_solver_nat is a STRICT MONOID HOMOMORPHISM:              *)
(*      n_axis (xs ++ ys) test = n_axis xs (n_axis ys test)           *)
(*    Universal, unconditional, function-level (with funext).         *)
(*                                                                    *)
(*    kleisli_full is a LOCALIZED MONOID HOMOMORPHISM:                *)
(*      When demo_lookup (xs ++ ys) test = None AND                  *)
(*           demo_lookup xs (n_axis ys test) = None AND              *)
(*           demo_lookup ys test = None,                              *)
(*      then kleisli_full (xs ++ ys) test                             *)
(*           = kleisli_full xs (kleisli_full ys test).               *)
(*    Off the demo set, full = n_axis. The localization is finite,  *)
(*    with support exactly equal to the demo input grids.             *)
(*                                                                    *)
(*  AT THE COLOR LEVEL:                                                *)
(*    Concrete instances close by reflexivity. The universal         *)
(*    statement requires a value-preservation lemma (proven here)   *)
(*    plus the specific transform's range-preservation property —    *)
(*    automatic for D₄ but general framework for arbitrary tasks.   *)
(*                                                                    *)
(*  EUCLIDEAN: the demo set is a finite set of "anchor" points on  *)
(*    the grid manifold. The full solver walks the geodesic UNLESS *)
(*    the test is at an anchor, in which case it teleports to the  *)
(*    cached destination. Off the anchor set, full = N-axis.        *)
(*                                                                    *)
(*  GAUSSIAN: the N-axis is a clean group homomorphism into Aut(    *)
(*    Grid). The full solver is a localization at the demo set —   *)
(*    formally, a quotient by "test = gi → answer = go" for each   *)
(*    (gi, go) in demos. The localization is finite, decidable,    *)
(*    and the decidable check is captured in demo_lookup_misses.   *)
(*                                                                    *)
(*  Uses functional_extensionality_dep for ONE function-level        *)
(*  identity. ZERO Admitted.                                          *)
(* ================================================================= *)
