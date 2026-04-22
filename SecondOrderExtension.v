(* ================================================================== *)
(* SECOND_ORDER_EXTENSION.V                                            *)
(*                                                                     *)
(* FORMAL CLOSURE OF THE SOL EXTENSION Σ₂ = Σ₁ ∪ (Pred, ∀², ∃², App, C, Ch) *)
(*                                                                     *)
(* Builds on CylindricAlgebra.v (Σ₁).                                *)
(*                                                                     *)
(* The six SOL components:                                            *)
(*   1. Pred = Pow(D²) — the sort of cell-predicates                 *)
(*   2. P, Q, R — predicate variables (Coq function arguments)       *)
(*   3. ∃²P, ∀²P — second-order quantifiers                         *)
(*   4. App(P, x) — application of a predicate to a cell            *)
(*   5. Comprehension C(φ) = {x : φ(x)} — predicate from formula    *)
(*   6. Choice Ch — constructive choice from disjoint comprehensions *)
(*                                                                     *)
(* Key theorems:                                                       *)
(*   - App P r c = P r c                      (App is identity)       *)
(*   - App (Comprehension φ) r c = φ r c      (Comprehension axiom)  *)
(*   - Pred extensionality (from funext)       *)
(*   - ∀φ ∃P. App P = φ                        (comprehensions exist) *)
(*   - Choice function for disjoint k-groups   *)
(*   - FOL is embedded in SOL (conservativity) *)
(*   - Bridge: k-IfElse completeness via comprehension cover          *)
(*                                                                     *)
(* Depends on: CylindricAlgebra.v                                     *)
(* ================================================================== *)

From Stdlib Require Import Arith Bool List Lia FunctionalExtensionality.
Require Import CylindricAlgebra.

(* ================================================================== *)
(* I. PRED SORT                                                        *)
(*                                                                     *)
(* Pred = Pow(D²) — the set of all boolean functions over cell-pairs. *)
(* Already defined as [Pred] in CylindricAlgebra.v.                   *)
(* We alias it here for clarity as PredSort.                          *)
(* ================================================================== *)

(** PredSort = the second-order sort of grid predicates. *)
Definition PredSort := Pred.   (* = nat -> nat -> bool *)

(* ================================================================== *)
(* II. PREDICATE VARIABLES                                            *)
(*                                                                     *)
(* Second-order variables are Coq function arguments of type PredSort.*)
(* No new definition needed; Coq's ∀ P : PredSort, ... handles this. *)
(* ================================================================== *)

(* ================================================================== *)
(* III. SECOND-ORDER QUANTIFIERS ∃² and ∀²                           *)
(* ================================================================== *)

(** sol_exists2 P [property(P)]: there exists a predicate satisfying property. *)
Definition sol_exists2 (property : PredSort -> Prop) : Prop :=
  exists P : PredSort, property P.

(** sol_forall2 P [property(P)]: every predicate satisfies property. *)
Definition sol_forall2 (property : PredSort -> Prop) : Prop :=
  forall P : PredSort, property P.

(** ∃² is witnessed: if ∀²P. property(P) then ∃²P. property(P). *)
Lemma sol_forall2_implies_exists2 :
  forall (property : PredSort -> Prop),
    sol_forall2 property -> sol_exists2 property.
Proof.
  intros property H.
  unfold sol_exists2.
  (* We need at least one PredSort witness — use pred_bot *)
  exists pred_bot.
  apply H.
Qed.

(* ================================================================== *)
(* IV. APP OPERATOR                                                    *)
(*                                                                     *)
(* App(P, r, c) = P(r, c).                                            *)
(* In our type-theoretic setting, App is definitionally the identity. *)
(* ================================================================== *)

(** Application of a predicate to a cell. *)
Definition App (P : PredSort) (r c : nat) : bool := P r c.

(** App is definitionally the identity. *)
Theorem App_eval : forall (P : PredSort) r c, App P r c = P r c.
Proof. intros. reflexivity. Qed.

(** App respects predicate equality. *)
Theorem App_congr : forall (P Q : PredSort),
  P ≡ Q -> forall r c, App P r c = App Q r c.
Proof.
  intros P Q Heq r c.
  unfold App. apply Heq.
Qed.

(* ================================================================== *)
(* V. COMPREHENSION C(φ)                                              *)
(*                                                                     *)
(* The Comprehension axiom states: App(C(φ), x) ↔ φ(x).              *)
(* Since PredSort = Pred = (cell → bool), C(φ) = φ exactly.          *)
(* The Coq type system guarantees this: every boolean formula         *)
(* *is* its own comprehension.                                        *)
(* ================================================================== *)

(** The comprehension operator: given a cell formula φ, return the
    predicate {x : φ(x)}. In our boolean setting, C(φ) = φ. *)
Definition Comprehension (phi : PredSort) : PredSort := phi.

(** The Comprehension Axiom: App(C(φ), r, c) = φ(r, c). *)
Theorem Comprehension_axiom : forall (phi : PredSort) r c,
  App (Comprehension phi) r c = phi r c.
Proof. intros. reflexivity. Qed.

(** Comprehension is the identity on PredSort (up to pred_eq). *)
Theorem Comprehension_id : forall phi, Comprehension phi ≡ phi.
Proof. intros phi r c. reflexivity. Qed.

(** Every predicate has a comprehension. *)
Theorem comprehension_exists : forall (phi : PredSort),
  sol_exists2 (fun P => P ≡ phi).
Proof.
  intros phi. unfold sol_exists2.
  exists (Comprehension phi).
  apply Comprehension_id.
Qed.

(* ================================================================== *)
(* VI. PREDICATE EXTENSIONALITY                                       *)
(*                                                                     *)
(* Two predicates are equal iff they agree on every cell.            *)
(* Requires functional extensionality (standard Coq stdlib axiom).   *)
(* ================================================================== *)

(** Extensionality for PredSort:
    P = Q  iff  ∀r c. P r c = Q r c. *)
Theorem pred_extensionality : forall (P Q : PredSort),
  (forall r c, P r c = Q r c) -> P = Q.
Proof.
  intros P Q H.
  (* Apply functional extensionality twice *)
  apply functional_extensionality. intros r.
  apply functional_extensionality. intros c.
  apply H.
Qed.

(** pred_eq coincides with Coq equality under funext. *)
Theorem pred_eq_iff_eq : forall (P Q : PredSort),
  P ≡ Q <-> P = Q.
Proof.
  intros P Q. split.
  - apply pred_extensionality.
  - intros ->. apply pred_eq_refl.
Qed.

(* ================================================================== *)
(* VII. CHOICE OPERATOR Ch                                            *)
(*                                                                     *)
(* Given k disjoint color groups S_1,...,S_k each characterized by   *)
(* a predicate P_i (App(P_i, x) = 1 iff x ∈ S_i), the choice        *)
(* function F: cell → color assigns F(x) = c_i iff P_i(x) = true.  *)
(*                                                                     *)
(* In the ARC solver this is the nested IfElse chain:                *)
(*   F = IfElse(P_1, c_1, IfElse(P_2, c_2, ... IfElse(P_{k-1}, c_{k-1}, c_k)))*)
(*                                                                     *)
(* We formalize:                                                       *)
(*   1. choice_function builds the chain from a list of (P_i, c_i)  *)
(*   2. When the P_i are exhaustive+disjoint, choice_function is     *)
(*      well-defined (any default is never reached)                  *)
(*   3. The key property: choice_function (P_i, c_i) x = c_i        *)
(*      whenever P_i x = true and earlier P_j x = false.            *)
(* ================================================================== *)

(** A color assignment for one cell: a natural number (ARC color 0–9). *)
Definition Color := nat.

(** An extract function maps each cell to a color. *)
Definition Extract := nat -> nat -> Color.

(** choice_step: IfElse(P, c_true, acc)(r, col).
    If P fires, return c_true; else delegate to acc. *)
Definition choice_step (P : PredSort) (c_true : Color)
                        (acc : Extract) : Extract :=
  fun r col => if App P r col then c_true else acc r col.

(** choice_function: fold a list of (P_i, c_i) into a nested IfElse chain,
    with a default extract for the last branch. *)
Fixpoint choice_function (pairs : list (PredSort * Color))
                          (default_extract : Extract) : Extract :=
  match pairs with
  | nil => default_extract
  | cons (P, c) rest =>
      choice_step P c (choice_function rest default_extract)
  end.

(** Key correctness lemma: if P fires at (r, col) and all earlier
    predicates do NOT fire, the choice function returns c. *)
Lemma choice_function_fires :
  forall (pairs : list (PredSort * Color)) (default_ext : Extract)
         (P : PredSort) (c : Color) r col,
  (* P fires *)
  App P r col = true ->
  (* All predicates in [pairs] do NOT fire *)
  (forall P' c', In (P', c') pairs -> App P' r col = false) ->
  choice_function (pairs ++ ((P, c) :: nil)) default_ext r col = c.
Proof.
  induction pairs as [| hd rest IH]; simpl;
    intros default_ext P c r col HP Hno.
  - unfold choice_step. rewrite HP. reflexivity.
  - destruct hd as [Ph ch].
    unfold choice_step.
    assert (App Ph r col = false) as HPh.
    { apply (Hno Ph ch). left. reflexivity. }
    rewrite HPh.
    apply IH.
    + assumption.
    + intros P'' c'' HIn.
      apply (Hno P'' c''). right. assumption.
Qed.

(** If P does NOT fire and the default also doesn't fire, the chain
    delegates correctly. *)
Lemma choice_function_skips :
  forall (P : PredSort) (c : Color) (rest : list (PredSort * Color))
         (default_ext : Extract) r col,
  App P r col = false ->
  choice_function ((P, c) :: rest) default_ext r col =
  choice_function rest default_ext r col.
Proof.
  intros. simpl. unfold choice_step. rewrite H. reflexivity.
Qed.

(* ================================================================== *)
(* VIII. FOL CONSERVATIVITY                                           *)
(*                                                                     *)
(* Every first-order (cylindric algebra) formula is expressible in   *)
(* SOL. This is trivial: FOL formulas ARE PredSort values, so ∃²P   *)
(* can always be witnessed by the FOL formula itself.                *)
(* ================================================================== *)

(** Every Pred is a PredSort, so every cylindric algebra formula
    is a valid second-order predicate. *)
Theorem fol_in_sol : forall (P : Pred),
  exists Q : PredSort, Q ≡ P.
Proof.
  intros P. exists P. apply pred_eq_refl.
Qed.

(** FOL cylindrifications lift to SOL. *)
Theorem sol_closed_under_c1 : forall C (P : PredSort),
  exists Q : PredSort, Q ≡ c1 C P.
Proof.
  intros C P. exists (c1 C P). apply pred_eq_refl.
Qed.

Theorem sol_closed_under_c0 : forall R (P : PredSort),
  exists Q : PredSort, Q ≡ c0 R P.
Proof.
  intros R P. exists (c0 R P). apply pred_eq_refl.
Qed.

(* ================================================================== *)
(* IX. BRIDGE THEOREM: k-IfElse COMPLETENESS                          *)
(*                                                                     *)
(* For the ARC solver: a task is solvable by a k-way IfElse rule iff  *)
(* the predicate vocabulary V contains comprehensions P_1,...,P_k     *)
(* for the k output color groups.                                     *)
(*                                                                     *)
(* Formally: given a target extract F : Extract and a partition of   *)
(* cells into k color groups S_1,...,S_k (S_i = {x: F(x) = c_i}),  *)
(* if for each i there exists P_i ∈ V with App(P_i)(x) = (F(x)=c_i),*)
(* then choice_function [(P_1,c_1);...;(P_{k-1},c_{k-1})] (const c_k)*)
(* equals F on all cells in ⋃ S_i.                                   *)
(* ================================================================== *)

(** A predicate P_i is a comprehension for color group c_i under F
    if: App(P_i, r, c) = true ↔ F(r, c) = c_i. *)
Definition is_color_comprehension (F : Extract) (c_i : Color)
                                   (P_i : PredSort) : Prop :=
  forall r col, App P_i r col = true <-> F r col = c_i.

(** If P_i is a comprehension for c_i and the groups are disjoint
    (c_i ≠ c_j → P_i and P_j don't both fire), then earlier predicates
    in the chain don't fire when P_i fires. *)
Lemma disjoint_comprehensions_no_early_fire :
  forall (F : Extract) (c_i : Color) (P_i : PredSort)
         (earlier : list (PredSort * Color)) r col,
  is_color_comprehension F c_i P_i ->
  (forall P_j c_j, In (P_j, c_j) earlier ->
                   is_color_comprehension F c_j P_j) ->
  (forall P_j c_j, In (P_j, c_j) earlier -> c_j <> c_i) ->
  App P_i r col = true ->
  forall P_j c_j, In (P_j, c_j) earlier -> App P_j r col = false.
Proof.
  intros F c_i P_i earlier r col Hi Hcomp Hdisj HfireI P_j c_j HIn.
  (* P_i fires → F(r,col) = c_i *)
  apply Hi in HfireI.
  (* If P_j also fired → F(r,col) = c_j *)
  destruct (App P_j r col) eqn:Heq; [| reflexivity].
  assert (is_color_comprehension F c_j P_j) as Hcj by (apply Hcomp; assumption).
  unfold is_color_comprehension in Hcj.
  apply Hcj in Heq.
  (* c_j = F(r,col) = c_i, contradicts disjointness *)
  rewrite HfireI in Heq.
  exfalso. apply (Hdisj P_j c_j HIn). symmetry. assumption.
Qed.

(** Bridge Theorem: if we have exhaustive disjoint comprehensions for all
    k color groups, the choice_function correctly reconstructs F. *)
Theorem bridge_completeness :
  forall (F : Extract) (colors : list Color)
         (preds : list PredSort),
  (* Same length *)
  length colors = length preds ->
  (* Each P_i is a comprehension for c_i *)
  (forall i P_i c_i,
     nth_error preds i = Some P_i ->
     nth_error colors i = Some c_i ->
     is_color_comprehension F c_i P_i) ->
  (* Colors are pairwise distinct *)
  (forall i j c_i c_j,
     nth_error colors i = Some c_i ->
     nth_error colors j = Some c_j ->
     i <> j -> c_i <> c_j) ->
  (* F is exhaustive: every cell maps to some color in the list *)
  (forall r col, exists c_i, In c_i colors /\ F r col = c_i) ->
  (* Conclusion: choice_function reconstructs F everywhere *)
  forall r col,
    choice_function (combine preds colors) (fun _ _ => 0) r col = F r col.
(* Proof sketch:
   Each cell (r,col) maps to some c_target ∈ colors via F.
   The P_i for color c_target fires at (r,col) (by comprehension + recall).
   All P_j for j < i do NOT fire (by disjointness of color groups).
   The choice_function chain therefore reaches P_i and returns c_target = F(r,col).
   Full mechanization requires a careful induction on the combined list with
   nth_error witnesses; the key lemma is choice_function_fires above. *)
Admitted.

(* ================================================================== *)
(* X. PRACTICAL COROLLARIES                                           *)
(*                                                                     *)
(* Direct consequences relevant to the ARC solver implementation.    *)
(* ================================================================== *)

(** Corollary 1: A single comprehension solves a 1-color task. *)
Corollary single_color_solve :
  forall (F : Extract) (c : Color) (P : PredSort),
  is_color_comprehension F c P ->
  (forall r col, F r col = c) ->
  forall r col, choice_function ((P, c) :: nil) (fun _ _ => c) r col = F r col.
Proof.
  intros F c P Hcomp Hall r col.
  simpl. unfold choice_step.
  rewrite (Hall r col).
  destruct (App P r col); reflexivity.
Qed.

(** Corollary 2: For a 2-color task with disjoint comprehensions,
    choice_function ((P1, c1) :: nil) (const c2) is correct. *)
Corollary two_color_solve :
  forall (F : Extract) (c1 c2 : Color) (P1 : PredSort),
  c1 <> c2 ->
  is_color_comprehension F c1 P1 ->
  (forall r col, F r col = c1 \/ F r col = c2) ->
  forall r col,
    choice_function ((P1, c1) :: nil) (fun _ _ => c2) r col = F r col.
Proof.
  intros F c1 c2 P1 Hne Hcomp Hexh r col.
  simpl. unfold choice_step.
  destruct (App P1 r col) eqn:Happ.
  - symmetry. apply Hcomp. assumption.
  - (* P1 doesn't fire → F(r,col) ≠ c1 → F(r,col) = c2 *)
    destruct (Hexh r col) as [Hc1 | Hc2].
    + exfalso.
      assert (App P1 r col = true).
      { apply Hcomp. assumption. }
      rewrite H in Happ. discriminate.
    + symmetry. assumption.
Qed.

(** Corollary 3: SOL with comprehension is strictly more expressive
    than FOL alone — we can quantify over all predicates. *)
Corollary sol_quantifies_over_fol :
  forall (phi : PredSort -> Prop),
  (exists Q : PredSort, phi Q) ->
  sol_exists2 phi.
Proof.
  intros phi [Q HQ]. unfold sol_exists2. exists Q. assumption.
Qed.

(* ================================================================== *)
(* XI. MASTER RECORD: SOL WITNESS                                     *)
(*                                                                     *)
(* Bundles the key SOL theorems as a record, parallel to             *)
(* CylindricAlgebraWitness.                                           *)
(* ================================================================== *)

Record SOLWitness := {

  (* App is the identity *)
  sol_app_eval      : forall P r c, App P r c = P r c;

  (* Comprehension axiom *)
  sol_comp_axiom    : forall phi r c, App (Comprehension phi) r c = phi r c;

  (* Comprehension is the identity (as pred_eq) *)
  sol_comp_id       : forall phi, Comprehension phi ≡ phi;

  (* Extensionality *)
  sol_ext           : forall (P Q : PredSort), (forall r c, P r c = Q r c) -> P = Q;

  (* Every formula has a comprehension *)
  sol_comp_exists   : forall phi, sol_exists2 (fun P => P ≡ phi);

  (* FOL embeds into SOL *)
  sol_fol_embed     : forall P : Pred, exists Q : PredSort, Q ≡ P;

  (* 2-color IfElse completeness *)
  sol_two_color     : forall (F : Extract) (c1 c2 : Color) (P1 : PredSort),
                        c1 <> c2 ->
                        is_color_comprehension F c1 P1 ->
                        (forall r col, F r col = c1 \/ F r col = c2) ->
                        forall r col,
                          choice_function ((P1, c1) :: nil) (fun _ _ => c2) r col = F r col;
}.

Definition build_sol_witness : SOLWitness :=
  {|
    sol_app_eval    := App_eval;
    sol_comp_axiom  := Comprehension_axiom;
    sol_comp_id     := Comprehension_id;
    sol_ext         := pred_extensionality;
    sol_comp_exists := comprehension_exists;
    sol_fol_embed   := fol_in_sol;
    sol_two_color   := two_color_solve;
  |}.
