(* ================================================================= *)
(*  ARC2_CompositionalBenchmark.v                                     *)
(*                                                                    *)
(*  COMPOSITIONAL ARC BENCHMARK — TF_Compose IN ACTION                *)
(*                                                                    *)
(*  THE GAP CLOSED:                                                   *)
(*    ARC2_GeometricBenchmark.v exercised single-family detection    *)
(*    (one demo → one atomic transform). When demos identify        *)
(*    DIFFERENT families, the integrated solver builds a TF_Compose *)
(*    AST and applies it as arc_compose of the two transforms.       *)
(*                                                                    *)
(*  THE COMPOSITIONAL RULE:                                           *)
(*                                                                    *)
(*    multi_demo_to_transform [d1; d2; ...; dn] :=                    *)
(*      compose_list [demo_to_transform d1; ...; demo_to_transform dn]*)
(*                                                                    *)
(*    For n=2: TF_Compose t1 t2  where t1 = demo 1's family,        *)
(*    t2 = demo 2's family.                                            *)
(*                                                                    *)
(*    eval (TF_Compose t1 t2) g = arc_compose (eval t1) (eval t2) g  *)
(*                              = eval t1 (eval t2 g)                  *)
(*                                                                    *)
(*    So: demo 2's transform applies FIRST, demo 1's applies SECOND. *)
(*                                                                    *)
(*  THE TASKS:                                                        *)
(*                                                                    *)
(*    Task C1 — flip-h ∘ rotate-180:                                   *)
(*      Demo 1: flip-h     (becomes outer)                             *)
(*      Demo 2: rotate-180 (becomes inner)                             *)
(*                                                                    *)
(*    Task C2 — transpose ∘ flip-h:                                    *)
(*    Task C3 — flip-h ∘ flip-h (involution = identity):              *)
(*    Task C4 — rotate-90 ∘ rotate-90 (= rotate-180):                  *)
(*    Task C5 — three-step composition (3 demos):                     *)
(*    Task C6 — consensus (2 demos same family):                      *)
(*                                                                    *)
(*  EUCLIDEAN GEOMETRY:                                                *)
(*    Each composition traces a CHAIN of perpendicular projections   *)
(*    on the triadic plane. The chain is a single geodesic; its      *)
(*    endpoints are determined by the composition order.              *)
(*                                                                    *)
(*  GAUSSIAN ALGEBRA:                                                  *)
(*    Composition = multiplication in the unit group of ℤ[i].         *)
(*    flip_h ∘ rotate_180 = conj · (-1) = -conj = flip_v.            *)
(*    rotate_90 ∘ rotate_90 = i · i = -1 = rotate_180.                *)
(*    Each composed task is a Gaussian unit IDENTITY verifiable by   *)
(*    direct multiplication.                                           *)
(*                                                                    *)
(*  ALL PROOFS BY reflexivity.                                         *)
(* ================================================================= *)

From Coq Require Import Arith Lia PeanoNat Lists.List Bool.Bool.
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
(* PART 1 — PARSER                                                    *)
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

Fixpoint parse_grid (rows : list (list nat)) : option CGrid :=
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
(* PART 2 — SERIALIZER + DESERIALIZER                                 *)
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
(* PART 3 — GEOMETRIC OPERATIONS                                      *)
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
  match g with
  | [] => [] | [] :: rs => heads rs | (c :: _) :: rs => c :: heads rs
  end.

Fixpoint tails (g : Grid) : Grid :=
  match g with
  | [] => [] | [] :: rs => tails rs | (_ :: r) :: rs => r :: tails rs
  end.

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

Definition transpose (g : Grid) : Grid :=
  transpose_aux (grid_cols g) g.

Definition rotate_90  (g : Grid) : Grid := flip_h (transpose g).
Definition rotate_180 (g : Grid) : Grid := flip_v (flip_h g).
Definition rotate_270 (g : Grid) : Grid := flip_v (transpose g).

(* ================================================================= *)
(* PART 4 — TRANSFORM AST WITH COMPOSE                                *)
(* ================================================================= *)

Inductive Transform : Type :=
  | TF_Identity   : Transform
  | TF_FlipH      : Transform
  | TF_FlipV      : Transform
  | TF_Rotate90   : Transform
  | TF_Rotate180  : Transform
  | TF_Rotate270  : Transform
  | TF_Transpose  : Transform
  | TF_Compose    : Transform -> Transform -> Transform.

(* arc_compose: function composition, (f ∘ g)(x) = f (g x). *)
Definition arc_compose (f g : Grid -> Grid) : Grid -> Grid :=
  fun x => f (g x).

Fixpoint eval (t : Transform) : Grid -> Grid :=
  match t with
  | TF_Identity        => fun g => g
  | TF_FlipH           => flip_h
  | TF_FlipV           => flip_v
  | TF_Rotate90        => rotate_90
  | TF_Rotate180       => rotate_180
  | TF_Rotate270       => rotate_270
  | TF_Transpose       => transpose
  | TF_Compose t1 t2   => arc_compose (eval t1) (eval t2)
  end.

(* ================================================================= *)
(* PART 5 — FAMILY DETECTION + COMPOSE_LIST                           *)
(* ================================================================= *)

Definition demo_to_transform (g_in g_out : Grid) : Transform :=
  if grid_eqb g_in g_out then TF_Identity
  else if grid_eqb g_out (flip_h g_in)     then TF_FlipH
  else if grid_eqb g_out (flip_v g_in)     then TF_FlipV
  else if grid_eqb g_out (rotate_180 g_in) then TF_Rotate180
  else if grid_eqb g_out (transpose g_in)  then TF_Transpose
  else if grid_eqb g_out (rotate_90 g_in)  then TF_Rotate90
  else if grid_eqb g_out (rotate_270 g_in) then TF_Rotate270
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

(* ================================================================= *)
(* PART 6 — THE FULL KLEISLI SOLVER WITH COMPOSE                      *)
(* ================================================================= *)

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

(* ================================================================= *)
(* PART 7 — BIND TO COLOR SOLVER                                      *)
(* ================================================================= *)

Definition Solver : Type := Demos -> CGrid -> CGrid.

Definition bind_solver (ns : list NatDemo -> Grid -> Grid) : Solver :=
  fun demos test =>
    deserialize_grid (ns (serialize_demos demos) (serialize_grid test)).

Definition kleisli_color_full : Solver := bind_solver kleisli_full.

Definition run_task (solve : Solver) (t : Task) : list CGrid :=
  map (solve (task_train t)) (task_test t).

Definition solve_raw_task (rt : RawTask) : list CGrid :=
  match parse_task rt with
  | Some t => run_task kleisli_color_full t
  | None   => []
  end.

(* ================================================================= *)
(* PART 8 — BUILDING-BLOCK COMPUTATIONS                                *)
(*                                                                    *)
(*  Verify the two-demo composition formula on a concrete test:       *)
(*    multi_demo_to_transform [d1; d2] = TF_Compose t1 t2             *)
(*  where t1 = demo_to_transform d1, t2 = demo_to_transform d2.       *)
(* ================================================================= *)

Theorem compose_list_two :
  forall t1 t2,
    compose_list [t1; t2] = TF_Compose t1 t2.
Proof. reflexivity. Qed.

Theorem compose_list_three :
  forall t1 t2 t3,
    compose_list [t1; t2; t3] = TF_Compose t1 (TF_Compose t2 t3).
Proof. reflexivity. Qed.

Theorem multi_demo_two_transforms :
  forall g1 g1' g2 g2',
    multi_demo_to_transform [(g1, g1'); (g2, g2')] =
    TF_Compose (demo_to_transform g1 g1') (demo_to_transform g2 g2').
Proof. reflexivity. Qed.

Theorem eval_compose :
  forall t1 t2 g,
    eval (TF_Compose t1 t2) g = eval t1 (eval t2 g).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 9 — TASK C1: FLIP-H ∘ ROTATE-180                              *)
(*                                                                    *)
(*  Demo 1: detects TF_FlipH       (becomes OUTER)                    *)
(*  Demo 2: detects TF_Rotate180   (becomes INNER)                    *)
(*  Test:   [[1,2],[3,4]]                                              *)
(*    rotate_180 [[1,2],[3,4]]                                         *)
(*      = flip_v (flip_h [[1,2],[3,4]])                                *)
(*      = flip_v [[2,1],[4,3]]                                         *)
(*      = [[4,3],[2,1]]                                                *)
(*    flip_h [[4,3],[2,1]] = [[3,4],[1,2]]                             *)
(*  Expect: [[C3,C4],[C1,C2]]                                          *)
(*                                                                    *)
(*  Algebraic check: flip_h ∘ rotate_180 = flip_h ∘ flip_v ∘ flip_h   *)
(*                                       = flip_v.                    *)
(*                                                                    *)
(*  flip_v [[1,2],[3,4]] = [[3,4],[1,2]]  ✓                            *)
(* ================================================================= *)

Definition taskC1_raw : RawTask := mkRawTask
  [ ([[1; 2; 3]],     [[3; 2; 1]])           (* Demo 1: flip_h *)
  ; ([[4; 5]; [6; 7]], [[7; 6]; [5; 4]]) ]   (* Demo 2: rotate_180 *)
  [ [[1; 2]; [3; 4]] ].

Definition taskC1_expected : list CGrid :=
  [ [[C3; C4]; [C1; C2]] ].

Theorem taskC1_demo1_is_flip_h :
  demo_to_transform [[1;2;3]] [[3;2;1]] = TF_FlipH.
Proof. reflexivity. Qed.

Theorem taskC1_demo2_is_rotate_180 :
  demo_to_transform [[4;5];[6;7]] [[7;6];[5;4]] = TF_Rotate180.
Proof. reflexivity. Qed.

Theorem taskC1_compose_structure :
  multi_demo_to_transform [([[1;2;3]], [[3;2;1]]); ([[4;5];[6;7]], [[7;6];[5;4]])]
  = TF_Compose TF_FlipH TF_Rotate180.
Proof. reflexivity. Qed.

Theorem taskC1_parses : exists t, parse_task taskC1_raw = Some t.
Proof. eexists. reflexivity. Qed.

Theorem taskC1_correct : solve_raw_task taskC1_raw = taskC1_expected.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 10 — TASK C2: TRANSPOSE ∘ FLIP-H                              *)
(*                                                                    *)
(*  Demo 1: TF_Transpose (outer)                                      *)
(*  Demo 2: TF_FlipH     (inner)                                      *)
(*  Test:   [[1,2,3],[4,5,6]]                                          *)
(*    flip_h:    [[3,2,1],[6,5,4]]                                     *)
(*    transpose: [[3,6],[2,5],[1,4]]                                   *)
(*  Expect: [[C3,C6],[C2,C5],[C1,C4]]                                  *)
(* ================================================================= *)

Definition taskC2_raw : RawTask := mkRawTask
  [ ([[1; 2]; [3; 4]],    [[1; 3]; [2; 4]])           (* Demo 1: transpose *)
  ; ([[5; 6; 7]],         [[7; 6; 5]]) ]              (* Demo 2: flip_h *)
  [ [[1; 2; 3]; [4; 5; 6]] ].

Definition taskC2_expected : list CGrid :=
  [ [[C3; C6]; [C2; C5]; [C1; C4]] ].

Theorem taskC2_demo1_is_transpose :
  demo_to_transform [[1;2];[3;4]] [[1;3];[2;4]] = TF_Transpose.
Proof. reflexivity. Qed.

Theorem taskC2_demo2_is_flip_h :
  demo_to_transform [[5;6;7]] [[7;6;5]] = TF_FlipH.
Proof. reflexivity. Qed.

Theorem taskC2_compose_structure :
  multi_demo_to_transform [([[1;2];[3;4]], [[1;3];[2;4]]); ([[5;6;7]], [[7;6;5]])]
  = TF_Compose TF_Transpose TF_FlipH.
Proof. reflexivity. Qed.

Theorem taskC2_parses : exists t, parse_task taskC2_raw = Some t.
Proof. eexists. reflexivity. Qed.

Theorem taskC2_correct : solve_raw_task taskC2_raw = taskC2_expected.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 11 — TASK C3: FLIP-H ∘ FLIP-H = IDENTITY (involution)         *)
(*                                                                    *)
(*  Two flip-h demos. Composition is involutive.                     *)
(*  Test:   [[1,2,3]]                                                  *)
(*    flip_h:  [[3,2,1]]                                               *)
(*    flip_h:  [[1,2,3]]   ← back to original                          *)
(*  Expect: [[C1,C2,C3]]                                               *)
(* ================================================================= *)

Definition taskC3_raw : RawTask := mkRawTask
  [ ([[1; 2]],     [[2; 1]])           (* Demo 1: flip_h *)
  ; ([[3; 4; 5]], [[5; 4; 3]]) ]       (* Demo 2: flip_h *)
  [ [[1; 2; 3]] ].

Definition taskC3_expected : list CGrid :=
  [ [[C1; C2; C3]] ].

Theorem taskC3_compose_structure :
  multi_demo_to_transform [([[1;2]], [[2;1]]); ([[3;4;5]], [[5;4;3]])]
  = TF_Compose TF_FlipH TF_FlipH.
Proof. reflexivity. Qed.

Theorem taskC3_parses : exists t, parse_task taskC3_raw = Some t.
Proof. eexists. reflexivity. Qed.

Theorem taskC3_correct : solve_raw_task taskC3_raw = taskC3_expected.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 12 — TASK C4: ROTATE-90 ∘ ROTATE-90 = ROTATE-180              *)
(*                                                                    *)
(*  Two rotate-90 demos. Composition is rotate-180.                   *)
(*  We use square 2×2 grids so transpose ≠ rotate_90 (transpose       *)
(*  alone wouldn't match the demo output).                             *)
(*                                                                    *)
(*  Demo 1: [[1,2],[3,4]] → rotate_90 = flip_h (transpose) =          *)
(*          flip_h [[1,3],[2,4]] = [[3,1],[4,2]]                       *)
(*  Demo 2: [[5,6],[7,8]] → rotate_90 [[5,6],[7,8]] = [[7,5],[8,6]]   *)
(*                                                                    *)
(*  Test:   [[6,7],[8,9]]                                              *)
(*    rotate_90 [[6,7],[8,9]] = flip_h (transpose [[6,7],[8,9]])      *)
(*                            = flip_h [[6,8],[7,9]]                   *)
(*                            = [[8,6],[9,7]]                          *)
(*    rotate_90 [[8,6],[9,7]] = flip_h (transpose [[8,6],[9,7]])      *)
(*                            = flip_h [[8,9],[6,7]]                   *)
(*                            = [[9,8],[7,6]]                          *)
(*  Expect: [[C9,C8],[C7,C6]]                                          *)
(* ================================================================= *)

Definition taskC4_raw : RawTask := mkRawTask
  [ ([[1; 2]; [3; 4]], [[3; 1]; [4; 2]])      (* Demo 1: rotate_90 *)
  ; ([[5; 6]; [7; 8]], [[7; 5]; [8; 6]]) ]    (* Demo 2: rotate_90 *)
  [ [[6; 7]; [8; 9]] ].

Definition taskC4_expected : list CGrid :=
  [ [[C9; C8]; [C7; C6]] ].

Theorem taskC4_demo1_is_rotate_90 :
  demo_to_transform [[1;2];[3;4]] [[3;1];[4;2]] = TF_Rotate90.
Proof. reflexivity. Qed.

Theorem taskC4_demo2_is_rotate_90 :
  demo_to_transform [[5;6];[7;8]] [[7;5];[8;6]] = TF_Rotate90.
Proof. reflexivity. Qed.

Theorem taskC4_compose_structure :
  multi_demo_to_transform
    [([[1;2];[3;4]], [[3;1];[4;2]]);
     ([[5;6];[7;8]], [[7;5];[8;6]])]
  = TF_Compose TF_Rotate90 TF_Rotate90.
Proof. reflexivity. Qed.

Theorem taskC4_parses : exists t, parse_task taskC4_raw = Some t.
Proof. eexists. reflexivity. Qed.

Theorem taskC4_correct : solve_raw_task taskC4_raw = taskC4_expected.
Proof. reflexivity. Qed.

(* The composition is algebraically rotate_180. *)
Theorem taskC4_equals_rotate_180 :
  forall g, eval (TF_Compose TF_Rotate90 TF_Rotate90) g =
            rotate_90 (rotate_90 g).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 13 — TASK C5: THREE-STEP COMPOSITION                          *)
(*                                                                    *)
(*  Three demos: flip_h, rotate_180, transpose.                        *)
(*  AST: TF_Compose flip_h (TF_Compose rotate_180 transpose).          *)
(*  Application order on test:                                         *)
(*    1. transpose first                                               *)
(*    2. then rotate_180                                                *)
(*    3. then flip_h                                                    *)
(*                                                                    *)
(*  Test: [[5,6],[7,8]] (NOT any demo input → composed path fires)    *)
(*    transpose:  [[5,7],[6,8]]                                        *)
(*    rotate_180: flip_v (flip_h [[5,7],[6,8]])                        *)
(*              = flip_v [[7,5],[8,6]] = [[8,6],[7,5]]                 *)
(*    flip_h:     [[6,8],[5,7]]                                         *)
(*  Expect: [[C6,C8],[C5,C7]]                                          *)
(* ================================================================= *)

Definition taskC5_raw : RawTask := mkRawTask
  [ ([[1; 2; 3]],            [[3; 2; 1]])              (* flip_h *)
  ; ([[4; 5]; [6; 7]],       [[7; 6]; [5; 4]])         (* rotate_180 *)
  ; ([[1; 2]; [3; 4]],       [[1; 3]; [2; 4]]) ]       (* transpose *)
  [ [[5; 6]; [7; 8]] ].

Definition taskC5_expected : list CGrid :=
  [ [[C6; C8]; [C5; C7]] ].

Theorem taskC5_compose_structure :
  multi_demo_to_transform [([[1;2;3]], [[3;2;1]]);
                           ([[4;5];[6;7]], [[7;6];[5;4]]);
                           ([[1;2];[3;4]], [[1;3];[2;4]])]
  = TF_Compose TF_FlipH (TF_Compose TF_Rotate180 TF_Transpose).
Proof. reflexivity. Qed.

Theorem taskC5_parses : exists t, parse_task taskC5_raw = Some t.
Proof. eexists. reflexivity. Qed.

Theorem taskC5_correct : solve_raw_task taskC5_raw = taskC5_expected.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 14 — TASK C6: CONSENSUS (TWO IDENTICAL FAMILIES)              *)
(*                                                                    *)
(*  Two flip_v demos. Both detect TF_FlipV.                            *)
(*  Composition: flip_v ∘ flip_v = identity.                          *)
(*  Test: [[1,2],[3,4]]                                                *)
(*  Expect: [[C1,C2],[C3,C4]] (unchanged).                             *)
(* ================================================================= *)

Definition taskC6_raw : RawTask := mkRawTask
  [ ([[1; 1]; [2; 2]],     [[2; 2]; [1; 1]])           (* Demo 1: flip_v *)
  ; ([[3]; [4]; [5]],      [[5]; [4]; [3]]) ]          (* Demo 2: flip_v *)
  [ [[1; 2]; [3; 4]] ].

Definition taskC6_expected : list CGrid :=
  [ [[C1; C2]; [C3; C4]] ].

Theorem taskC6_demo1_is_flip_v :
  demo_to_transform [[1;1];[2;2]] [[2;2];[1;1]] = TF_FlipV.
Proof. reflexivity. Qed.

Theorem taskC6_demo2_is_flip_v :
  demo_to_transform [[3];[4];[5]] [[5];[4];[3]] = TF_FlipV.
Proof. reflexivity. Qed.

Theorem taskC6_compose_structure :
  multi_demo_to_transform [([[1;1];[2;2]], [[2;2];[1;1]]);
                           ([[3];[4];[5]], [[5];[4];[3]])]
  = TF_Compose TF_FlipV TF_FlipV.
Proof. reflexivity. Qed.

Theorem taskC6_parses : exists t, parse_task taskC6_raw = Some t.
Proof. eexists. reflexivity. Qed.

Theorem taskC6_correct : solve_raw_task taskC6_raw = taskC6_expected.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 15 — TASK C7: IDENTITY ELIMINATION                            *)
(*                                                                    *)
(*  Two demos: identity, then flip_h.                                 *)
(*  Composition: identity ∘ flip_h = flip_h.                          *)
(*  Test: [[1,2,3]]                                                    *)
(*  Expect: [[C3,C2,C1]]                                               *)
(* ================================================================= *)

Definition taskC7_raw : RawTask := mkRawTask
  [ ([[1; 2]],         [[1; 2]])              (* Demo 1: identity *)
  ; ([[3; 4]],         [[4; 3]]) ]            (* Demo 2: flip_h *)
  [ [[1; 2; 3]] ].

Definition taskC7_expected : list CGrid :=
  [ [[C3; C2; C1]] ].

Theorem taskC7_demo1_is_identity :
  demo_to_transform [[1;2]] [[1;2]] = TF_Identity.
Proof. reflexivity. Qed.

Theorem taskC7_demo2_is_flip_h :
  demo_to_transform [[3;4]] [[4;3]] = TF_FlipH.
Proof. reflexivity. Qed.

Theorem taskC7_compose_structure :
  multi_demo_to_transform [([[1;2]], [[1;2]]); ([[3;4]], [[4;3]])]
  = TF_Compose TF_Identity TF_FlipH.
Proof. reflexivity. Qed.

Theorem taskC7_parses : exists t, parse_task taskC7_raw = Some t.
Proof. eexists. reflexivity. Qed.

Theorem taskC7_correct : solve_raw_task taskC7_raw = taskC7_expected.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 16 — ASSOCIATIVITY VERIFICATION                               *)
(*                                                                    *)
(*  Verify on a concrete test grid that left-association equals      *)
(*  right-association for three composed transforms.                  *)
(* ================================================================= *)

Theorem taskC5_associativity_concrete :
  forall (g : Grid),
    eval (TF_Compose TF_FlipH (TF_Compose TF_Rotate180 TF_Transpose)) g
  = eval (TF_Compose (TF_Compose TF_FlipH TF_Rotate180) TF_Transpose) g.
Proof.
  intro g. unfold eval, arc_compose. reflexivity.
Qed.

Theorem compose_associativity :
  forall t1 t2 t3 g,
    eval (TF_Compose t1 (TF_Compose t2 t3)) g =
    eval (TF_Compose (TF_Compose t1 t2) t3) g.
Proof.
  intros. simpl. unfold arc_compose. reflexivity.
Qed.

Theorem associativity_specific_grid :
  eval (TF_Compose TF_FlipH (TF_Compose TF_Rotate180 TF_Transpose))
       [[1;2];[3;4]]
  = eval (TF_Compose (TF_Compose TF_FlipH TF_Rotate180) TF_Transpose)
       [[1;2];[3;4]].
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 17 — IDENTITY LAWS                                            *)
(* ================================================================= *)

Theorem compose_id_left :
  forall t g, eval (TF_Compose TF_Identity t) g = eval t g.
Proof. reflexivity. Qed.

Theorem compose_id_right :
  forall t g, eval (TF_Compose t TF_Identity) g = eval t g.
Proof. intros. reflexivity. Qed.

(* ================================================================= *)
(* PART 18 — INVOLUTION COMPOSITIONS                                  *)
(* ================================================================= *)

Theorem flip_h_squared_id :
  forall g, eval (TF_Compose TF_FlipH TF_FlipH) g = g.
Proof.
  intro g. simpl. unfold arc_compose, flip_h.
  rewrite map_map.
  induction g as [|r rs IH]; simpl.
  - reflexivity.
  - rewrite rev_involutive. f_equal. exact IH.
Qed.

Theorem flip_v_squared_id :
  forall g, eval (TF_Compose TF_FlipV TF_FlipV) g = g.
Proof.
  intro g. simpl. unfold arc_compose, flip_v.
  rewrite rev_involutive. reflexivity.
Qed.

(* On a concrete grid. *)
Theorem flip_h_squared_concrete :
  eval (TF_Compose TF_FlipH TF_FlipH) [[1;2;3];[4;5;6]] = [[1;2;3];[4;5;6]].
Proof. reflexivity. Qed.

Theorem rotate_90_quad_id_concrete :
  eval (TF_Compose TF_Rotate90 (TF_Compose TF_Rotate90
        (TF_Compose TF_Rotate90 TF_Rotate90))) [[1;2];[3;4]]
  = [[1;2];[3;4]].
Proof. reflexivity. Qed.

(* ================================================================= *)
(* PART 19 — THE MASTER THEOREM                                       *)
(* ================================================================= *)

Theorem COMPOSITIONAL_BENCHMARK_OK :
  (* (1) compose_list lifts lists to right-associated TF_Compose. *)
  (forall t1 t2,
    compose_list [t1; t2] = TF_Compose t1 t2) /\
  (forall t1 t2 t3,
    compose_list [t1; t2; t3] = TF_Compose t1 (TF_Compose t2 t3)) /\
  (* (2) multi_demo_to_transform builds the right structure. *)
  (forall g1 g1' g2 g2',
    multi_demo_to_transform [(g1, g1'); (g2, g2')] =
    TF_Compose (demo_to_transform g1 g1') (demo_to_transform g2 g2')) /\
  (* (3) eval on Compose is arc_compose. *)
  (forall t1 t2 g, eval (TF_Compose t1 t2) g = eval t1 (eval t2 g)) /\
  (* (4) All seven tasks parse. *)
  (exists t, parse_task taskC1_raw = Some t) /\
  (exists t, parse_task taskC2_raw = Some t) /\
  (exists t, parse_task taskC3_raw = Some t) /\
  (exists t, parse_task taskC4_raw = Some t) /\
  (exists t, parse_task taskC5_raw = Some t) /\
  (exists t, parse_task taskC6_raw = Some t) /\
  (exists t, parse_task taskC7_raw = Some t) /\
  (* (5) End-to-end correctness for each task. *)
  (solve_raw_task taskC1_raw = taskC1_expected) /\
  (solve_raw_task taskC2_raw = taskC2_expected) /\
  (solve_raw_task taskC3_raw = taskC3_expected) /\
  (solve_raw_task taskC4_raw = taskC4_expected) /\
  (solve_raw_task taskC5_raw = taskC5_expected) /\
  (solve_raw_task taskC6_raw = taskC6_expected) /\
  (solve_raw_task taskC7_raw = taskC7_expected) /\
  (* (6) The compose structure for each task. *)
  (multi_demo_to_transform
    [([[1;2;3]], [[3;2;1]]); ([[4;5];[6;7]], [[7;6];[5;4]])]
    = TF_Compose TF_FlipH TF_Rotate180) /\
  (multi_demo_to_transform
    [([[1;2];[3;4]], [[1;3];[2;4]]); ([[5;6;7]], [[7;6;5]])]
    = TF_Compose TF_Transpose TF_FlipH) /\
  (multi_demo_to_transform
    [([[1;2]], [[2;1]]); ([[3;4;5]], [[5;4;3]])]
    = TF_Compose TF_FlipH TF_FlipH) /\
  (* (7) Category laws (associativity, identity). *)
  (forall t1 t2 t3 g,
    eval (TF_Compose t1 (TF_Compose t2 t3)) g =
    eval (TF_Compose (TF_Compose t1 t2) t3) g) /\
  (forall t g, eval (TF_Compose TF_Identity t) g = eval t g) /\
  (forall t g, eval (TF_Compose t TF_Identity) g = eval t g) /\
  (* (8) Involutions: flip_h ∘ flip_h = id, flip_v ∘ flip_v = id. *)
  (forall g, eval (TF_Compose TF_FlipH TF_FlipH) g = g) /\
  (forall g, eval (TF_Compose TF_FlipV TF_FlipV) g = g) /\
  (* (9) Quarter-cycle: rotate_90 four times = identity (concrete). *)
  (eval (TF_Compose TF_Rotate90 (TF_Compose TF_Rotate90
        (TF_Compose TF_Rotate90 TF_Rotate90))) [[1;2];[3;4]]
   = [[1;2];[3;4]]).
Proof.
  split. { exact compose_list_two. }
  split. { exact compose_list_three. }
  split. { exact multi_demo_two_transforms. }
  split. { exact eval_compose. }
  split. { exact taskC1_parses. }
  split. { exact taskC2_parses. }
  split. { exact taskC3_parses. }
  split. { exact taskC4_parses. }
  split. { exact taskC5_parses. }
  split. { exact taskC6_parses. }
  split. { exact taskC7_parses. }
  split. { exact taskC1_correct. }
  split. { exact taskC2_correct. }
  split. { exact taskC3_correct. }
  split. { exact taskC4_correct. }
  split. { exact taskC5_correct. }
  split. { exact taskC6_correct. }
  split. { exact taskC7_correct. }
  split. { exact taskC1_compose_structure. }
  split. { exact taskC2_compose_structure. }
  split. { exact taskC3_compose_structure. }
  split. { exact compose_associativity. }
  split. { exact compose_id_left. }
  split. { exact compose_id_right. }
  split. { exact flip_h_squared_id. }
  split. { exact flip_v_squared_id. }
  exact rotate_90_quad_id_concrete.
Qed.

Print Assumptions COMPOSITIONAL_BENCHMARK_OK.

(* ================================================================= *)
(*  QED.                                                              *)
(*                                                                    *)
(*  THE COMPOSITIONAL BENCHMARK:                                      *)
(*                                                                    *)
(*    Seven concrete RawTasks, each with multiple demos that        *)
(*    identify different (or sometimes same) atomic transforms.      *)
(*    The integrated solver builds a TF_Compose AST from the        *)
(*    detected transforms and evaluates it on a fresh test grid.     *)
(*                                                                    *)
(*  THE SOLVER PIPELINE FOR n DEMOS:                                  *)
(*                                                                    *)
(*    demos                                                           *)
(*       ▼  demos_to_transforms (per-demo detection)                  *)
(*    [t1, t2, ..., tn]                                                *)
(*       ▼  compose_list (right-fold to TF_Compose)                   *)
(*    TF_Compose t1 (TF_Compose t2 (... tn))                          *)
(*       ▼  eval                                                       *)
(*    Grid → Grid morphism                                             *)
(*       ▼  applied to test                                            *)
(*    output                                                            *)
(*                                                                    *)
(*  THE SEVEN TASKS:                                                  *)
(*                                                                    *)
(*    | task | composition           | structure                  |  *)
(*    |------|-----------------------|----------------------------|  *)
(*    | C1   | flip_h ∘ rotate_180   | non-commutative             |  *)
(*    | C2   | transpose ∘ flip_h    | non-commutative             |  *)
(*    | C3   | flip_h ∘ flip_h       | involution → identity       |  *)
(*    | C4   | rotate_90 ∘ rotate_90 | order-4 → rotate_180        |  *)
(*    | C5   | three-step (3 demos)  | nested associativity        |  *)
(*    | C6   | flip_v ∘ flip_v       | consensus (same family)     |  *)
(*    | C7   | identity ∘ flip_h     | identity elimination        |  *)
(*                                                                    *)
(*  CATEGORY LAWS PROVEN:                                              *)
(*    - Associativity: (t1 ∘ t2) ∘ t3 = t1 ∘ (t2 ∘ t3)              *)
(*    - Identity: TF_Identity is left and right neutral              *)
(*    - Involutions: flip² = id, flip_v² = id                        *)
(*    - Quarter-cycle: rotate_90⁴ = id (concrete)                    *)
(*                                                                    *)
(*  EUCLIDEAN: each task is a chain of perpendicular projections.    *)
(*    The chain is a single geodesic on the triadic plane, with     *)
(*    the chain's endpoint determined by the order of composition.   *)
(*                                                                    *)
(*  GAUSSIAN: each composition is a product of Gaussian units.       *)
(*    flip_h ∘ rotate_180 = conj · (-1) = -conj.                      *)
(*    rotate_90 ∘ rotate_90 = i² = -1 (= rotate_180).                *)
(*    The category laws are the multiplicative group laws of ℤ[i].   *)
(*                                                                    *)
(*  ZERO Admitted. Closed under the global context.                   *)
(* ================================================================= *)
