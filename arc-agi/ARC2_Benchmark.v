(* ================================================================= *)
(*  ARC2_Benchmark.v                                                  *)
(*                                                                    *)
(*  END-TO-END ARC BENCHMARK IN COQ                                   *)
(*                                                                    *)
(*  THE GOAL:                                                         *)
(*    Demonstrate the full ARC pipeline on concrete tasks, with     *)
(*    every step verified by Coq:                                     *)
(*                                                                    *)
(*      Raw JSON-shaped data (RawTask)                                *)
(*         │                                                          *)
(*         ▼  parse_task                                              *)
(*      Typed Color10 Task                                            *)
(*         │                                                          *)
(*         ▼  run_task kleisli_color_solver                           *)
(*      Color10 outputs                                                *)
(*         │                                                          *)
(*         ▼  reflexivity check                                        *)
(*      Expected outputs (provably equal)                              *)
(*                                                                    *)
(*  THE FIVE TASKS:                                                   *)
(*                                                                    *)
(*    Task 1 — IDENTITY:        copy input to output                  *)
(*    Task 2 — DEMO RECOVERY:   test = demo input → output is demo    *)
(*    Task 3 — DEMO RECOVERY 2: 2 demos, test matches second demo    *)
(*    Task 4 — DEMO PASS:       multiple test inputs, each = a demo  *)
(*    Task 5 — UNKNOWN TEST:    test ≠ any demo input → return test  *)
(*                                                                    *)
(*  Each is a self-contained proof: parse the raw JSON, run the      *)
(*  solver, verify by reflexivity that the result matches the         *)
(*  expected output.                                                   *)
(*                                                                    *)
(*  EUCLIDEAN GEOMETRY:                                                *)
(*    Each benchmark traces a single geodesic from raw-data →         *)
(*    chromatic → solver → chromatic. The reflexivity check verifies *)
(*    the geodesic is closed (round-trip lands on the expected       *)
(*    Color10 grid).                                                   *)
(*                                                                    *)
(*  GAUSSIAN ALGEBRA:                                                  *)
(*    Each benchmark is a Gaussian unit operation: identity, demo    *)
(*    lookup (the I-axis hit), or pass-through. Reflexivity verifies *)
(*    the conjugation σ⁻¹ ∘ ns ∘ σ produces the expected result.    *)
(*                                                                    *)
(*  ALL PROOFS BY reflexivity OR direct construction. ZERO Admitted. *)
(* ================================================================= *)

From Coq Require Import Arith Lia PeanoNat Lists.List Bool.Bool.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(* PART 0 — LOCAL DEFINITIONS (REIMPORT)                              *)
(*                                                                    *)
(*  We reimport the minimal types and functions from the reader     *)
(*  + runner so this file compiles independently.                     *)
(* ================================================================= *)

Inductive Color10 : Type :=
  | C0  : Color10 | C1  : Color10 | C2  : Color10 | C3  : Color10
  | C4  : Color10 | C5  : Color10 | C6  : Color10 | C7  : Color10
  | C8  : Color10 | C9  : Color10.

Definition color10_eqb (c1 c2 : Color10) : bool :=
  match c1, c2 with
  | C0, C0 => true | C1, C1 => true | C2, C2 => true
  | C3, C3 => true | C4, C4 => true | C5, C5 => true
  | C6, C6 => true | C7, C7 => true | C8, C8 => true
  | C9, C9 => true | _, _ => false
  end.

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

(* Color10 grid types. *)
Definition CGrid := list (list Color10).
Definition Demo  := (CGrid * CGrid)%type.
Definition Demos := list Demo.

(* Raw nat grid types. *)
Definition Grid := list (list nat).
Definition NatDemo := (Grid * Grid)%type.

(* Raw task types. *)
Definition RawDemo := (Grid * Grid)%type.

Record RawTask : Type := mkRawTask {
  raw_train : list RawDemo;
  raw_test  : list Grid
}.

Record Task : Type := mkTask {
  task_train : Demos;
  task_test  : list CGrid
}.

(* ================================================================= *)
(* PART 1 — PARSER (reader internals)                                 *)
(* ================================================================= *)

Fixpoint parse_row (xs : list nat) : option (list Color10) :=
  match xs with
  | []        => Some []
  | x :: rest =>
      match nat_to_color x, parse_row rest with
      | Some c, Some cs => Some (c :: cs)
      | _, _            => None
      end
  end.

Fixpoint parse_grid (rows : list (list nat)) :
    option CGrid :=
  match rows with
  | []        => Some []
  | r :: rest =>
      match parse_row r, parse_grid rest with
      | Some cr, Some crest => Some (cr :: crest)
      | _, _                => None
      end
  end.

Definition parse_demo (rd : RawDemo) : option Demo :=
  let (rin, rout) := rd in
  match parse_grid rin, parse_grid rout with
  | Some gin, Some gout => Some (gin, gout)
  | _, _                => None
  end.

Fixpoint parse_demos (rds : list RawDemo) : option Demos :=
  match rds with
  | []       => Some []
  | rd :: rs =>
      match parse_demo rd, parse_demos rs with
      | Some d, Some ds => Some (d :: ds)
      | _, _            => None
      end
  end.

Fixpoint parse_tests (rts : list Grid) : option (list CGrid) :=
  match rts with
  | []        => Some []
  | rt :: rs  =>
      match parse_grid rt, parse_tests rs with
      | Some t, Some ts => Some (t :: ts)
      | _, _            => None
      end
  end.

Definition parse_task (rt : RawTask) : option Task :=
  match parse_demos (raw_train rt), parse_tests (raw_test rt) with
  | Some demos, Some tests => Some (mkTask demos tests)
  | _, _                   => None
  end.

(* ================================================================= *)
(* PART 2 — SERIALIZER + DESERIALIZER (runner internals)              *)
(* ================================================================= *)

Definition serialize_row (cs : list Color10) : list nat :=
  map color_to_nat cs.

Definition serialize_grid (g : CGrid) : Grid :=
  map serialize_row g.

Definition serialize_demo (d : Demo) : NatDemo :=
  let (gi, go) := d in (serialize_grid gi, serialize_grid go).

Definition serialize_demos (ds : Demos) : list NatDemo :=
  map serialize_demo ds.

Definition deserialize_row (xs : list nat) : list Color10 :=
  map nat_to_color_total xs.

Definition deserialize_grid (g : Grid) : CGrid :=
  map deserialize_row g.

(* ================================================================= *)
(* PART 3 — THE NAT-GRID SOLVER                                       *)
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

Fixpoint demo_lookup (xs : list NatDemo) (g : Grid) : option Grid :=
  match xs with
  | [] => None
  | (gi, go) :: rest =>
      if grid_eqb g gi then Some go else demo_lookup rest g
  end.

Definition NatSolver : Type := list NatDemo -> Grid -> Grid.

Definition demo_lookup_solver : NatSolver :=
  fun demos test =>
    match demo_lookup demos test with
    | Some go => go
    | None    => test
    end.

(* ================================================================= *)
(* PART 4 — THE BOUND COLOR SOLVER                                    *)
(* ================================================================= *)

Definition Solver : Type := Demos -> CGrid -> CGrid.

Definition bind_solver (ns : NatSolver) : Solver :=
  fun demos test =>
    deserialize_grid (ns (serialize_demos demos) (serialize_grid test)).

Definition kleisli_color_solver : Solver :=
  bind_solver demo_lookup_solver.

Definition run_task (solve : Solver) (t : Task) : list CGrid :=
  map (solve (task_train t)) (task_test t).

(* ================================================================= *)
(* PART 5 — TASK 1: PURE IDENTITY                                     *)
(*                                                                    *)
(*  One demo: input = output (a 2×2 grid of blue/red).                *)
(*  One test: same as the demo input.                                  *)
(*  Expected: the demo output (= input).                               *)
(*                                                                    *)
(*  Demonstrates: the I-axis hit (test exactly matches demo input).  *)
(* ================================================================= *)

Definition task1_raw : RawTask := mkRawTask
  [ ([[1; 2]; [2; 1]], [[1; 2]; [2; 1]]) ]   (* identity demo *)
  [ [[1; 2]; [2; 1]] ].                       (* test = demo input *)

Definition task1_expected : list CGrid :=
  [ [[C1; C2]; [C2; C1]] ].

Theorem task1_parses :
  exists t, parse_task task1_raw = Some t.
Proof.
  unfold parse_task, task1_raw. simpl.
  eexists. reflexivity.
Qed.

Theorem task1_solver_correct :
  match parse_task task1_raw with
  | Some t => run_task kleisli_color_solver t = task1_expected
  | None   => False
  end.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 6 — TASK 2: DEMO RECOVERY (DIFFERENT INPUT/OUTPUT)            *)
(*                                                                    *)
(*  One demo: 2×2 grid maps to a different 2×2 grid.                  *)
(*  One test: same as demo input.                                      *)
(*  Expected: the demo output.                                         *)
(*                                                                    *)
(*  Demonstrates: kleisli_color_solver hits the I-axis on a non-     *)
(*  trivial transform.                                                 *)
(* ================================================================= *)

Definition task2_raw : RawTask := mkRawTask
  [ ([[1; 2]; [3; 4]], [[5; 6]; [7; 8]]) ]   (* arbitrary demo *)
  [ [[1; 2]; [3; 4]] ].                       (* test = demo input *)

Definition task2_expected : list CGrid :=
  [ [[C5; C6]; [C7; C8]] ].

Theorem task2_parses :
  exists t, parse_task task2_raw = Some t.
Proof.
  unfold parse_task, task2_raw. simpl.
  eexists. reflexivity.
Qed.

Theorem task2_solver_correct :
  match parse_task task2_raw with
  | Some t => run_task kleisli_color_solver t = task2_expected
  | None   => False
  end.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 7 — TASK 3: DEMO RECOVERY ON THE SECOND DEMO                  *)
(*                                                                    *)
(*  Two demos.                                                         *)
(*  One test: matches the SECOND demo input.                           *)
(*  Expected: the second demo's output.                                *)
(*                                                                    *)
(*  Demonstrates: demo_lookup walks past the first demo and finds    *)
(*  the matching one further along.                                    *)
(* ================================================================= *)

Definition task3_raw : RawTask := mkRawTask
  [ ([[1; 1]; [1; 1]], [[2; 2]; [2; 2]])    (* demo A *)
  ; ([[3; 3]; [3; 3]], [[4; 4]; [4; 4]]) ]  (* demo B *)
  [ [[3; 3]; [3; 3]] ].                       (* test = demo B input *)

Definition task3_expected : list CGrid :=
  [ [[C4; C4]; [C4; C4]] ].

Theorem task3_parses :
  exists t, parse_task task3_raw = Some t.
Proof.
  unfold parse_task, task3_raw. simpl.
  eexists. reflexivity.
Qed.

Theorem task3_solver_correct :
  match parse_task task3_raw with
  | Some t => run_task kleisli_color_solver t = task3_expected
  | None   => False
  end.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 8 — TASK 4: MULTIPLE TESTS, EACH MATCHES A DEMO               *)
(*                                                                    *)
(*  Two demos, two tests. Each test matches a different demo input. *)
(*  Expected: an output for each test (in test order).                *)
(*                                                                    *)
(*  Demonstrates: run_task processes all tests independently.          *)
(* ================================================================= *)

Definition task4_raw : RawTask := mkRawTask
  [ ([[1]], [[5]])     (* demo A: blue → gray *)
  ; ([[2]], [[6]]) ]   (* demo B: red → magenta *)
  [ [[1]]              (* test 1: blue *)
  ; [[2]] ].           (* test 2: red *)

Definition task4_expected : list CGrid :=
  [ [[C5]]   (* output 1: gray *)
  ; [[C6]]   (* output 2: magenta *)
  ].

Theorem task4_parses :
  exists t, parse_task task4_raw = Some t.
Proof.
  unfold parse_task, task4_raw. simpl.
  eexists. reflexivity.
Qed.

Theorem task4_solver_correct :
  match parse_task task4_raw with
  | Some t => run_task kleisli_color_solver t = task4_expected
  | None   => False
  end.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 9 — TASK 5: UNKNOWN TEST (NOT IN DEMOS)                       *)
(*                                                                    *)
(*  One demo. The test grid does NOT match the demo input.           *)
(*  Expected: kleisli_color_solver falls through to returning the    *)
(*  test grid unchanged (the F-axis fallback).                         *)
(*                                                                    *)
(*  Demonstrates: graceful fallback when no demo matches.              *)
(* ================================================================= *)

Definition task5_raw : RawTask := mkRawTask
  [ ([[1; 1]], [[2; 2]]) ]   (* demo: [1,1] → [2,2] *)
  [ [[7; 8; 9]] ].             (* test: [7,8,9] — different shape *)

Definition task5_expected : list CGrid :=
  [ [[C7; C8; C9]] ].   (* fallback: return test unchanged *)

Theorem task5_parses :
  exists t, parse_task task5_raw = Some t.
Proof.
  unfold parse_task, task5_raw. simpl.
  eexists. reflexivity.
Qed.

Theorem task5_solver_correct :
  match parse_task task5_raw with
  | Some t => run_task kleisli_color_solver t = task5_expected
  | None   => False
  end.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 10 — STRUCTURAL PROPERTIES OF EACH TASK                       *)
(* ================================================================= *)

(* Each task parses to a Task with the right shape. *)
Theorem task1_train_count :
  match parse_task task1_raw with
  | Some t => length (task_train t) = 1
  | None   => False
  end.
Proof. reflexivity. Qed.

Theorem task1_test_count :
  match parse_task task1_raw with
  | Some t => length (task_test t) = 1
  | None   => False
  end.
Proof. reflexivity. Qed.

Theorem task3_train_count :
  match parse_task task3_raw with
  | Some t => length (task_train t) = 2
  | None   => False
  end.
Proof. reflexivity. Qed.

Theorem task4_test_count :
  match parse_task task4_raw with
  | Some t => length (task_test t) = 2
  | None   => False
  end.
Proof. reflexivity. Qed.

(* Output count matches test count for every task. *)
Theorem task1_output_count :
  match parse_task task1_raw with
  | Some t => length (run_task kleisli_color_solver t) = length (task_test t)
  | None   => False
  end.
Proof. reflexivity. Qed.

Theorem task4_output_count :
  match parse_task task4_raw with
  | Some t => length (run_task kleisli_color_solver t) = length (task_test t)
  | None   => False
  end.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 11 — COMPOSITE: PARSE-AND-RUN AS A SINGLE COMPUTATION         *)
(*                                                                    *)
(*  An end-to-end function that takes a RawTask, parses it, runs the *)
(*  solver, and returns the outputs (or [] on parse failure).         *)
(* ================================================================= *)

Definition solve_raw_task (rt : RawTask) : list CGrid :=
  match parse_task rt with
  | Some t => run_task kleisli_color_solver t
  | None   => []
  end.

Theorem solve_raw_task1 : solve_raw_task task1_raw = task1_expected.
Proof. reflexivity. Qed.

Theorem solve_raw_task2 : solve_raw_task task2_raw = task2_expected.
Proof. reflexivity. Qed.

Theorem solve_raw_task3 : solve_raw_task task3_raw = task3_expected.
Proof. reflexivity. Qed.

Theorem solve_raw_task4 : solve_raw_task task4_raw = task4_expected.
Proof. reflexivity. Qed.

Theorem solve_raw_task5 : solve_raw_task task5_raw = task5_expected.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 12 — INVALID INPUT REJECTION                                  *)
(*                                                                    *)
(*  When the raw task contains values >= 10, parsing fails and       *)
(*  solve_raw_task returns []. We verify rejection on a malformed   *)
(*  input.                                                             *)
(* ================================================================= *)

Definition task_invalid : RawTask := mkRawTask
  [ ([[10]], [[11]]) ]   (* values >= 10 — invalid *)
  [ [[1]] ].

Theorem task_invalid_parse_fails :
  parse_task task_invalid = None.
Proof. reflexivity. Qed.

Theorem solve_invalid_returns_empty :
  solve_raw_task task_invalid = [].
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 13 — TASK STATISTICS                                          *)
(* ================================================================= *)

(* Count the number of cells across all train demos in a task. *)
Definition raw_task_demo_count (rt : RawTask) : nat :=
  length (raw_train rt).

Definition raw_task_test_count (rt : RawTask) : nat :=
  length (raw_test rt).

(* Concrete counts. *)
Theorem task1_stats : raw_task_demo_count task1_raw = 1 /\
                      raw_task_test_count task1_raw = 1.
Proof. split; reflexivity. Qed.

Theorem task3_stats : raw_task_demo_count task3_raw = 2 /\
                      raw_task_test_count task3_raw = 1.
Proof. split; reflexivity. Qed.

Theorem task4_stats : raw_task_demo_count task4_raw = 2 /\
                      raw_task_test_count task4_raw = 2.
Proof. split; reflexivity. Qed.

(* ================================================================= *)
(* PART 14 — THE MASTER THEOREM                                       *)
(* ================================================================= *)

Theorem ARC_BENCHMARK_OK :
  (* (1) All five valid tasks parse successfully. *)
  (exists t, parse_task task1_raw = Some t) /\
  (exists t, parse_task task2_raw = Some t) /\
  (exists t, parse_task task3_raw = Some t) /\
  (exists t, parse_task task4_raw = Some t) /\
  (exists t, parse_task task5_raw = Some t) /\
  (* (2) The invalid task is rejected. *)
  (parse_task task_invalid = None) /\
  (* (3) End-to-end correctness for each task. *)
  (solve_raw_task task1_raw = task1_expected) /\
  (solve_raw_task task2_raw = task2_expected) /\
  (solve_raw_task task3_raw = task3_expected) /\
  (solve_raw_task task4_raw = task4_expected) /\
  (solve_raw_task task5_raw = task5_expected) /\
  (* (4) The invalid task returns the empty output list. *)
  (solve_raw_task task_invalid = []) /\
  (* (5) Output count matches test count for every valid task. *)
  (length (solve_raw_task task1_raw) = raw_task_test_count task1_raw) /\
  (length (solve_raw_task task2_raw) = raw_task_test_count task2_raw) /\
  (length (solve_raw_task task3_raw) = raw_task_test_count task3_raw) /\
  (length (solve_raw_task task4_raw) = raw_task_test_count task4_raw) /\
  (length (solve_raw_task task5_raw) = raw_task_test_count task5_raw) /\
  (* (6) Demo counts. *)
  (raw_task_demo_count task1_raw = 1) /\
  (raw_task_demo_count task3_raw = 2) /\
  (raw_task_demo_count task4_raw = 2) /\
  (* (7) Test counts. *)
  (raw_task_test_count task1_raw = 1) /\
  (raw_task_test_count task4_raw = 2).
Proof.
  split. { exact task1_parses. }
  split. { exact task2_parses. }
  split. { exact task3_parses. }
  split. { exact task4_parses. }
  split. { exact task5_parses. }
  split. { exact task_invalid_parse_fails. }
  split. { exact solve_raw_task1. }
  split. { exact solve_raw_task2. }
  split. { exact solve_raw_task3. }
  split. { exact solve_raw_task4. }
  split. { exact solve_raw_task5. }
  split. { exact solve_invalid_returns_empty. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  reflexivity.
Qed.

Print Assumptions ARC_BENCHMARK_OK.

(* ================================================================= *)
(*  QED.                                                              *)
(*                                                                    *)
(*  THE END-TO-END ARC BENCHMARK:                                     *)
(*                                                                    *)
(*    Five concrete RawTasks, each paired with an expected output.   *)
(*    Each is verified end-to-end by reflexivity:                     *)
(*                                                                    *)
(*      Raw JSON → parse_task → run_task kleisli_color_solver →      *)
(*      check against expected → reflexivity.                          *)
(*                                                                    *)
(*  TASK 1 — IDENTITY:                                                *)
(*    Demo (2×2): [[1,2],[2,1]] → [[1,2],[2,1]]                       *)
(*    Test:       [[1,2],[2,1]]                                       *)
(*    Expected:   [[C1,C2],[C2,C1]]    ✓                              *)
(*                                                                    *)
(*  TASK 2 — DEMO RECOVERY (NON-TRIVIAL):                             *)
(*    Demo (2×2): [[1,2],[3,4]] → [[5,6],[7,8]]                       *)
(*    Test:       [[1,2],[3,4]]                                       *)
(*    Expected:   [[C5,C6],[C7,C8]]    ✓                              *)
(*                                                                    *)
(*  TASK 3 — DEMO RECOVERY (SECOND DEMO):                             *)
(*    Demos:      [[1,1],[1,1]]→[[2,2],[2,2]],                        *)
(*                [[3,3],[3,3]]→[[4,4],[4,4]]                         *)
(*    Test:       [[3,3],[3,3]]                                       *)
(*    Expected:   [[C4,C4],[C4,C4]]    ✓                              *)
(*                                                                    *)
(*  TASK 4 — MULTIPLE TESTS:                                          *)
(*    Demos:      [[1]]→[[5]], [[2]]→[[6]]                            *)
(*    Tests:      [[1]], [[2]]                                         *)
(*    Expected:   [[C5]], [[C6]]       ✓                              *)
(*                                                                    *)
(*  TASK 5 — UNKNOWN TEST (FALLBACK):                                 *)
(*    Demo:       [[1,1]] → [[2,2]]                                   *)
(*    Test:       [[7,8,9]] (different shape, no match)               *)
(*    Expected:   [[C7,C8,C9]] (passthrough)  ✓                       *)
(*                                                                    *)
(*  INVALID TASK:                                                     *)
(*    Demo:       [[10]] → [[11]] (out of color range)                *)
(*    parse_task returns None;  solve_raw_task returns []   ✓         *)
(*                                                                    *)
(*  EUCLIDEAN: each benchmark traces a closed geodesic from the raw  *)
(*    data manifold to the chromatic manifold, through the solver,   *)
(*    and back. Closed = the round-trip lands on the expected grid.  *)
(*                                                                    *)
(*  GAUSSIAN: each task is a Gaussian unit operation conjugated      *)
(*    through σ : Color10 → nat. Reflexivity verifies σ⁻¹ ∘ ns ∘ σ.  *)
(*                                                                    *)
(*  ZERO Admitted. Closed under the global context.                   *)
(* ================================================================= *)
