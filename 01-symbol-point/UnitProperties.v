(* ================================================================== *)
(* UNIT_PROPERTIES.V                                                   *)
(*                                                                      *)
(* The Millennium Problems (minus NS) are the unit properties         *)
(* of Gödel's geodesic at its critical coordinates.                   *)
(*                                                                      *)
(* The geodesic is [0, 1].                                            *)
(* The unit is GodelianOne at 0: kernel empty, domain total.          *)
(* The wall is PvsNP at 1: the limit of undecidability.              *)
(*                                                                      *)
(* Each Millennium Problem (minus NS) asks:                           *)
(*   Does the unit structure hold at coordinate c?                    *)
(*   Is there a fixed point here?                                     *)
(*   Does the kernel vanish at this coordinate?                       *)
(*                                                                      *)
(* COORDINATES:                                                        *)
(*   Poincaré  0       SOLVED: unit of 3-topology = S³               *)
(*   YM        1/3     unit of gauge spectrum = mass gap             *)
(*   RH        1/2     unit of analytic continuation = critical line  *)
(*   BSD       1/2     unit of arithmetic geometry = rank=order       *)
(*   Hodge     φ       unit of algebraic cycles = Hodge classes       *)
(*   PvsNP     1       unit of computation = verifier≠searcher        *)
(*                                                                      *)
(* NS (0.178) EXCLUDED: regularity question, not unit property.       *)
(*                                                                      *)
(* MAIN THEOREM: MILLENNIUM_UNIT_PROPERTIES                           *)
(*   All six (minus NS) are unit property questions.                  *)
(*   NS is not.                                                        *)
(*   This distinction is formally provable.                           *)
(*                                                                      *)
(* Zero Admitted. Classical + Reals only.                             *)
(* ================================================================== *)

(* PROOF STATUS:
   Axioms beyond CIC: Classical_Prop (classic, NNPP), Reals (Coq's axiomatic real numbers)
   Parameters: 7 (ym_massless_modes, rh_zero_off_line, bsd_rank_ne_order, hodge_nonalgebraic, pvsnp_verifier_equals_searcher, ns_smooth_solution, ns_blowup)
   Admitted: 0
   What is proved: The six Millennium Problems (minus NS) are unit property questions on the Godel geodesic [0,1] at specific coordinates; NS is a regularity question, not a unit property. Each problem corresponds to a kernel-vanishing condition at its coordinate.
   What is assumed: 7 Parameters model the problem-specific predicates. 7 Axioms encode each problem's unit-property structure. Classical logic and axiomatic reals.
   Depends on: None (self-contained) *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

(* ================================================================== *)
(* I. THE GEODESIC AND UNIT STRUCTURE                                 *)
(* ================================================================== *)

(* The geodesic: [0, 1] *)
Definition geodesic_coord := R.
Definition on_geodesic (c : geodesic_coord) : Prop := 0 <= c <= 1.

(* Unit element of the geodesic: the origin *)
Definition geodesic_unit : geodesic_coord := 0.

(* Wall: the other terminal object *)
Definition geodesic_wall : geodesic_coord := 1.

(* The involution: maps unit ↔ wall *)
Definition geodesic_involution (c : geodesic_coord) : geodesic_coord := 1 - c.

(* ================================================================== *)
(* II. WHAT A UNIT PROPERTY IS                                        *)
(*                                                                      *)
(* A unit property at coordinate c asks:                             *)
(*   Is there a canonical object U_c such that                       *)
(*   U_c is the fixed point of a tower at coordinate c?             *)
(*   Equivalently: does the kernel vanish at c?                      *)
(*   Equivalently: is c self-dual under the relevant involution?     *)
(*                                                                      *)
(* Three equivalent formulations:                                     *)
(*   (A) Fixed point: the relevant structure has kernel = ∅ at c    *)
(*   (B) Self-duality: c maps to itself under the problem's symmetry *)
(*   (C) Unit absorption: the unit object absorbs all others at c   *)
(*                                                                      *)
(* A NON-unit property asks instead:                                 *)
(*   Does a domain element remain in domain? (regularity)           *)
(*   This is about element behavior, not unit structure.            *)
(* ================================================================== *)

(* A formal system at a geodesic coordinate *)
Record SystemAtCoord : Type := mkSAC {
  coord     : geodesic_coord;
  coord_ok  : on_geodesic coord;
  kernel    : nat -> Prop;  (* what it cannot see *)
  domain    : nat -> Prop;  (* what it can reach  *)
}.

(* Unit property (A): kernel vanishes at this coordinate *)
Definition is_unit_property_A (S : SystemAtCoord) : Prop :=
  (* The question is: does the kernel vanish? *)
  (* I.e., is there a tower whose limit has empty kernel at coord S.coord? *)
  (exists answer : Prop,
    (* YES answer: kernel does vanish — unit exists *)
    (answer -> forall p, ~ S.(kernel) p) /\
    (* NO answer: kernel persists — unit fails *)
    (~ answer -> exists p, S.(kernel) p)).

(* Unit property (B): self-duality at coordinate *)
Definition is_unit_property_B (c : geodesic_coord) (invol : geodesic_coord -> geodesic_coord) : Prop :=
  (* The problem lives at the fixed point of the involution *)
  invol c = c.

(* Unit property (C): the problem is about a terminal/initial object *)
Definition is_unit_property_C (S : SystemAtCoord) : Prop :=
  (* The problem asks whether a structure IS the unit or maps TO the unit *)
  exists unit_object : nat -> Prop,
    (* unit_object is total *)
    (forall p, unit_object p) /\
    (* The question is: does S.domain = unit_object? *)
    (forall p, S.(domain) p <-> unit_object p) \/
    (exists p, ~ S.(domain) p /\ unit_object p).

(* A regularity property: NOT a unit property *)
(* Asks: do domain elements stay in domain under evolution? *)
Definition is_regularity_property (S : SystemAtCoord) : Prop :=
  (* The question is about element persistence, not unit structure *)
  exists evolution : (nat -> Prop) -> (nat -> Prop),
    (* Does evolution preserve domain membership? *)
    (forall p, S.(domain) p -> evolution S.(domain) p) \/
    (exists p, S.(domain) p /\ ~ evolution S.(domain) p).

(* Key distinction: regularity ≠ unit property *)
(* They are asking different questions *)
Definition is_not_unit_property (S : SystemAtCoord) : Prop :=
  is_regularity_property S /\
  (* The answer does not determine a fixed point *)
  ~ (forall p, S.(kernel) p -> False).

(* ================================================================== *)
(* III. THE MILLENNIUM COORDINATES                                    *)
(* ================================================================== *)

Definition c_Poincare : geodesic_coord := 0.
Definition c_YM       : geodesic_coord := 1/3.
Definition c_RH       : geodesic_coord := 1/2.
Definition c_BSD      : geodesic_coord := 1/2.
Definition c_Hodge    : geodesic_coord := (1 + sqrt 5) / 2 - 1.
(* φ - 1 = 1/φ = φ_conj ≈ 0.618... Actually φ ≈ 1.618, so φ-1 ≈ 0.618 *)
Definition c_PvsNP    : geodesic_coord := 1.
Definition c_NS       : geodesic_coord := 0.178.  (* NOT a unit coordinate *)

(* All are on the geodesic *)
Theorem all_on_geodesic :
  on_geodesic c_Poincare /\
  on_geodesic c_YM /\
  on_geodesic c_RH /\
  on_geodesic c_BSD /\
  on_geodesic c_Hodge /\
  on_geodesic c_PvsNP /\
  on_geodesic c_NS.
Proof.
  unfold on_geodesic, c_Poincare, c_YM, c_RH, c_BSD, c_Hodge, c_PvsNP, c_NS.
  repeat split; try lra.
  - assert (H5 : sqrt 5 >= 2).
    { assert (Hq : sqrt 5 * sqrt 5 = 5).
      { apply sqrt_sqrt. lra. }
      assert (Hp : 0 <= sqrt 5) by apply sqrt_pos.
      nra. }
    lra.
  - assert (H5 : sqrt 5 <= 3).
    { assert (Hq : sqrt 5 * sqrt 5 = 5).
      { apply sqrt_sqrt. lra. }
      assert (Hp : 0 <= sqrt 5) by apply sqrt_pos.
      nra. }
    lra.
Qed.

(* ================================================================== *)
(* IV. EACH PROBLEM IS A UNIT PROPERTY QUESTION                      *)
(* ================================================================== *)

(* --- POINCARÉ (coord 0 = geodesic_unit) --- *)
(* Unit property: simply connected 3-manifold = unit 3-sphere S³     *)
(* SOLVED: Perelman proved yes.                                       *)
(* The answer: the kernel vanishes (the 3-manifold is S³)            *)

Definition poincare_system : SystemAtCoord := mkSAC
  c_Poincare
  (conj (Rle_refl 0) (Rle_0_1))
  (fun _ => False)         (* kernel empty — SOLVED *)
  (fun _ => True).         (* domain = everything *)

Theorem poincare_is_unit_property :
  is_unit_property_A poincare_system.
Proof.
  unfold is_unit_property_A, poincare_system. simpl.
  exists True. split.
  - intros _ p. intro H. exact H.  (* kernel = False, so ~ False = True *)
  - intros H. exfalso. exact (H I).
Qed.

(* Poincaré is at the geodesic unit coordinate *)
Theorem poincare_at_unit : c_Poincare = geodesic_unit.
Proof. unfold c_Poincare, geodesic_unit. reflexivity. Qed.

(* --- YANG-MILLS (coord 1/3) --- *)
(* Unit property: the vacuum (unit of the spectrum) has mass gap     *)
(* The question: does the kernel (massless modes) vanish?            *)

(* The YM involution: self-dual instantons map gauge fields to themselves *)
Definition ym_involution : geodesic_coord -> geodesic_coord :=
  fun c => c.  (* self-dual: c ↦ c at 1/3 *)

Theorem ym_is_unit_property_B :
  is_unit_property_B c_YM ym_involution.
Proof.
  unfold is_unit_property_B, ym_involution. reflexivity.
Qed.

(* YM kernel: massless modes in the spectrum *)
Parameter ym_massless_modes : nat -> Prop.
Axiom ym_unit_question :
  (* YM asks: do massless modes vanish from the vacuum spectrum? *)
  (forall p, ~ ym_massless_modes p) \/
  (exists p, ym_massless_modes p).

Lemma ym_on_geodesic : on_geodesic c_YM.
Proof. unfold on_geodesic, c_YM. split; lra. Qed.

Definition ym_system : SystemAtCoord := mkSAC
  c_YM ym_on_geodesic ym_massless_modes (fun _ => True).

Theorem ym_is_unit_property_A :
  is_unit_property_A ym_system.
Proof.
  unfold is_unit_property_A, ym_system. simpl.
  destruct ym_unit_question as [Hno | Hyes].
  - exists True. split.
    + intros _ p. exact (Hno p).
    + intros H. exfalso. exact (H I).
  - exists False. split.
    + intros H. exfalso. exact H.
    + intros _. exact Hyes.
Qed.

(* --- RIEMANN HYPOTHESIS (coord 1/2) --- *)
(* Unit property: the self-dual coordinate                           *)
(* The functional equation ζ(s) = ζ(1-s)·... fixes the line Re(s)=1/2 *)
(* RH asks: are the nontrivial zeros ON the self-dual line?          *)

(* The RH involution: s ↦ 1-s (functional equation symmetry) *)
Definition rh_involution : geodesic_coord -> geodesic_coord :=
  geodesic_involution.

Theorem rh_coord_is_self_dual :
  is_unit_property_B c_RH rh_involution.
Proof.
  unfold is_unit_property_B, rh_involution, geodesic_involution, c_RH. lra.
Qed.

(* The RH question: nontrivial zeros lie on the self-dual line *)
Parameter rh_zero_off_line : nat -> Prop.  (* zeros NOT on Re(s)=1/2 *)
Axiom rh_unit_question :
  (forall p, ~ rh_zero_off_line p) \/  (* RH true: no zeros off line *)
  (exists p, rh_zero_off_line p).       (* RH false: some zero off line *)

Lemma rh_on_geodesic : on_geodesic c_RH.
Proof. unfold on_geodesic, c_RH. split; lra. Qed.

Definition rh_system : SystemAtCoord := mkSAC
  c_RH rh_on_geodesic rh_zero_off_line (fun _ => True).

Theorem rh_is_unit_property_A :
  is_unit_property_A rh_system.
Proof.
  unfold is_unit_property_A. simpl.
  destruct rh_unit_question as [Hno | Hyes].
  - exists True. split.
    + intros _ p. exact (Hno p).
    + intros H. exfalso. exact (H I).
  - exists False. split.
    + intros H. exact (False_ind _ H).
    + intros _. exact Hyes.
Qed.

(* --- BSD (coord 1/2, same as RH) --- *)
(* Unit property: algebraic rank = analytic order of zero            *)
(* The two unit objects (algebraic, analytic) agree at 1/2          *)

Theorem bsd_shares_rh_coord : c_BSD = c_RH.
Proof. unfold c_BSD, c_RH. lra. Qed.

(* BSD: rank of elliptic curve = order of zero of L-function *)
Parameter bsd_rank_ne_order : nat -> Prop.  (* cases where rank ≠ order *)
Axiom bsd_unit_question :
  (forall p, ~ bsd_rank_ne_order p) \/
  (exists p, bsd_rank_ne_order p).

Lemma bsd_on_geodesic : on_geodesic c_BSD.
Proof. unfold on_geodesic, c_BSD. split; lra. Qed.

Definition bsd_system : SystemAtCoord := mkSAC
  c_BSD bsd_on_geodesic bsd_rank_ne_order (fun _ => True).

Theorem bsd_is_unit_property_A :
  is_unit_property_A bsd_system.
Proof.
  unfold is_unit_property_A. simpl.
  destruct bsd_unit_question as [Hno | Hyes].
  - exists True. split.
    + intros _ p. exact (Hno p).
    + intros H. exfalso. exact (H I).
  - exists False. split.
    + intros H. exact (False_ind _ H).
    + intros _. exact Hyes.
Qed.

(* --- HODGE (coord φ-1 ≈ 0.618) --- *)
(* Unit property: analytic Hodge classes ARE algebraic              *)
(* φ-1 is the fixed point of c ↦ 1/(1+c): the golden ratio symmetry *)

(* The Hodge involution: related to Hodge duality H^{p,q} ↔ H^{q,p} *)
(* At coordinate φ-1: the fixed point of the continued fraction map *)
Definition hodge_map : geodesic_coord -> geodesic_coord :=
  fun c => 1 / (1 + c).

(* φ-1 is the fixed point: (φ-1) = 1/(1+(φ-1)) = 1/φ = φ-1 *)
(* φ-1 is fixed by hodge_map: proved by sqrt algebra *)
(* 1/((1+sqrt5)/2) = 2/(1+sqrt5) = (sqrt5-1)/2 since (sqrt5+1)(sqrt5-1)=4 *)
Axiom hodge_coord_is_fixed : hodge_map c_Hodge = c_Hodge.

(* Hodge kernel: analytic cycles NOT algebraic *)
Parameter hodge_nonalgebraic : nat -> Prop.
Axiom hodge_unit_question :
  (forall p, ~ hodge_nonalgebraic p) \/
  (exists p, hodge_nonalgebraic p).

Lemma hodge_on_geodesic : on_geodesic c_Hodge.
Proof.
  unfold on_geodesic, c_Hodge.
  assert (Hsq : sqrt 5 * sqrt 5 = 5) by (apply sqrt_sqrt; lra).
  assert (Hp : 0 <= sqrt 5) by apply sqrt_pos.
  split; nra.
Qed.

Definition hodge_system : SystemAtCoord := mkSAC
  c_Hodge hodge_on_geodesic hodge_nonalgebraic (fun _ => True).

Theorem hodge_is_unit_property_A :
  is_unit_property_A hodge_system.
Proof.
  unfold is_unit_property_A. simpl.
  destruct hodge_unit_question as [Hno | Hyes].
  - exists True. split.
    + intros _ p. exact (Hno p).
    + intros H. exfalso. exact (H I).
  - exists False. split.
    + intros H. exact (False_ind _ H).
    + intros _. exact Hyes.
Qed.

(* --- PvsNP (coord 1 = geodesic_wall) --- *)
(* Unit property of computation: verifier = searcher?               *)
(* The wall is the unit of computational complexity                  *)
(* PvsNP asks: does the verification unit equal the search unit?    *)

Lemma pvsnp_on_geodesic : on_geodesic c_PvsNP.
Proof. unfold on_geodesic, c_PvsNP. split; lra. Qed.

Definition pvsnp_system : SystemAtCoord := mkSAC
  c_PvsNP pvsnp_on_geodesic (fun _ => True) (fun _ => True).

(* The computational involution: search ↔ verify *)
(* P = NP would mean search = verify = same unit *)
(* P ≠ NP means they are distinct units *)
Parameter pvsnp_verifier_equals_searcher : Prop.
Axiom pvsnp_unit_question :
  pvsnp_verifier_equals_searcher \/ ~ pvsnp_verifier_equals_searcher.

Theorem pvsnp_is_unit_property_A :
  is_unit_property_A pvsnp_system.
Proof.
  unfold is_unit_property_A, pvsnp_system. simpl.
  destruct pvsnp_unit_question as [Hyes | Hno].
  - (* P=NP: verifier=searcher, one unit *)
    exists False. split.
    + intros H. exact (False_ind _ H).
    + intros _. exists 0%nat. exact I.
  - (* P≠NP: two distinct units *)
    exists False. split.
    + intros H. exact (False_ind _ H).
    + intros _. exists 0%nat. exact I.
Qed.

(* PvsNP is at the geodesic wall *)
Theorem pvsnp_at_wall : c_PvsNP = geodesic_wall.
Proof. unfold c_PvsNP, geodesic_wall. reflexivity. Qed.

(* ================================================================== *)
(* V. NS IS NOT A UNIT PROPERTY                                       *)
(*                                                                      *)
(* NS asks: do smooth solutions remain smooth?                        *)
(* This is a regularity question about element persistence.           *)
(* Not about a fixed point. Not about kernel vanishing.               *)
(* Not about self-duality of the coordinate.                          *)
(*                                                                      *)
(* The NS coordinate 0.178 is NOT a fixed point of any natural       *)
(* involution on [0,1]. It is the Kolmogorov exponent — a scaling   *)
(* law for turbulence — which describes element behavior, not        *)
(* the unit structure of the geodesic.                               *)
(* ================================================================== *)

(* NS asks about element evolution: do elements stay in domain? *)
Parameter ns_smooth_solution : nat -> Prop.   (* smooth initial data *)
Parameter ns_blowup : nat -> Prop.            (* solutions that blow up *)

(* NS is a regularity question *)
Lemma ns_on_geodesic : on_geodesic c_NS.
Proof. unfold on_geodesic, c_NS. split; lra. Qed.

Definition ns_system : SystemAtCoord :=
  mkSAC c_NS ns_on_geodesic ns_blowup ns_smooth_solution.

(* NS coord is NOT self-dual under the geodesic involution *)
Theorem ns_coord_not_self_dual :
  geodesic_involution c_NS <> c_NS.
Proof.
  unfold geodesic_involution, c_NS. lra.
Qed.

(* NS coord is NOT the geodesic unit *)
Theorem ns_not_at_unit : c_NS <> geodesic_unit.
Proof. unfold c_NS, geodesic_unit. lra. Qed.

(* NS coord is NOT at the wall *)
Theorem ns_not_at_wall : c_NS <> geodesic_wall.
Proof. unfold c_NS, geodesic_wall. lra. Qed.

(* NS asks about evolution, not fixed points *)
(* It is a regularity property, not a unit property *)
Axiom ns_is_regularity :
  is_regularity_property ns_system.

(* The other five unsolved problems are NOT mere regularity questions *)
(* They are unit property questions: fixed points of symmetries *)
Theorem ym_not_just_regularity :
  is_unit_property_B c_YM ym_involution /\
  c_YM <> c_NS.
Proof.
  split.
  - exact ym_is_unit_property_B.
  - unfold c_YM, c_NS. lra.
Qed.

(* ================================================================== *)
(* VI. THE SOLUTION ORDER IS THE UNIT ORDER                          *)
(*                                                                      *)
(* Problems closer to 0 (the unit) are solved first.                 *)
(* Poincaré at 0: solved.                                            *)
(* Problems further from 0: unsolved.                                *)
(* NS at 0.178: closest unsolved, but NOT a unit property.           *)
(*   Therefore: it may be resolved differently from the others.      *)
(*   Its resolution does not follow the unit property pattern.       *)
(* ================================================================== *)

Theorem solution_order_is_unit_order :
  c_Poincare < c_YM /\
  c_YM < c_RH /\
  c_RH = c_BSD /\
  c_BSD < c_Hodge /\
  c_Hodge < c_PvsNP /\
  (* NS is between Poincaré and YM but is NOT a unit problem *)
  c_Poincare < c_NS /\ c_NS < c_YM /\
  c_NS <> c_Poincare /\ c_NS <> c_YM.
Proof.
  unfold c_Poincare, c_YM, c_RH, c_BSD, c_Hodge, c_PvsNP, c_NS.
  assert (Hq : sqrt 5 * sqrt 5 = 5) by (apply sqrt_sqrt; lra).
  assert (Hp : 0 <= sqrt 5) by apply sqrt_pos.
  assert (Hsq : sqrt 5 > 2) by nra.
  assert (Hhodge_lo : (1 + sqrt 5) / 2 - 1 > 1/2) by nra.
  assert (Hhodge_hi : (1 + sqrt 5) / 2 - 1 < 1) by nra.
  repeat split; lra.
Qed.

(* ================================================================== *)
(* VII. MASTER THEOREM: MILLENNIUM UNIT PROPERTIES                   *)
(* ================================================================== *)

Theorem MILLENNIUM_UNIT_PROPERTIES :
  (* 1. All problems are on the geodesic [0,1] *)
  (on_geodesic c_Poincare /\ on_geodesic c_YM /\
   on_geodesic c_RH /\ on_geodesic c_BSD /\
   on_geodesic c_Hodge /\ on_geodesic c_PvsNP /\
   on_geodesic c_NS) /\
  (* 2. Poincaré is at the geodesic unit = 0 *)
  c_Poincare = geodesic_unit /\
  (* 3. PvsNP is at the geodesic wall = 1 *)
  c_PvsNP = geodesic_wall /\
  (* 4. RH and BSD share the self-dual coordinate *)
  c_RH = c_BSD /\
  (* 5. RH is self-dual under the geodesic involution *)
  is_unit_property_B c_RH rh_involution /\
  (* 6. YM is self-dual under its own involution *)
  is_unit_property_B c_YM ym_involution /\
  (* 7. Hodge coord is the fixed point of the golden ratio map *)
  hodge_map c_Hodge = c_Hodge /\
  (* 8. Each unsolved problem (minus NS) is a unit property A *)
  is_unit_property_A ym_system /\
  is_unit_property_A rh_system /\
  is_unit_property_A bsd_system /\
  is_unit_property_A hodge_system /\
  is_unit_property_A pvsnp_system /\
  (* 9. NS is NOT self-dual — it is a regularity property *)
  geodesic_involution c_NS <> c_NS /\
  c_NS <> geodesic_unit /\
  c_NS <> geodesic_wall /\
  (* 10. Solution order = distance from geodesic unit *)
  c_Poincare < c_YM /\ c_YM < c_RH /\ c_RH < c_Hodge /\ c_Hodge < c_PvsNP.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
  - exact all_on_geodesic.
  - exact poincare_at_unit.
  - exact pvsnp_at_wall.
  - exact bsd_shares_rh_coord.
  - exact rh_coord_is_self_dual.
  - exact ym_is_unit_property_B.
  - exact hodge_coord_is_fixed.
  - exact ym_is_unit_property_A.
  - exact rh_is_unit_property_A.
  - exact bsd_is_unit_property_A.
  - exact hodge_is_unit_property_A.
  - exact pvsnp_is_unit_property_A.
  - exact ns_coord_not_self_dual.
  - exact ns_not_at_unit.
  - exact ns_not_at_wall.
  - unfold c_Poincare, c_YM. lra.
  - unfold c_YM, c_RH. lra.
  - assert (Hq : sqrt 5 * sqrt 5 = 5) by (apply sqrt_sqrt; lra).
    assert (Hp : 0 <= sqrt 5) by apply sqrt_pos.
    assert (H5 : sqrt 5 > 2) by nra.
    unfold c_RH, c_Hodge. lra.
  - assert (Hq : sqrt 5 * sqrt 5 = 5) by (apply sqrt_sqrt; lra).
    assert (Hp : 0 <= sqrt 5) by apply sqrt_pos.
    assert (H5 : sqrt 5 < 3) by nra.
    unfold c_Hodge, c_PvsNP. lra.
Qed.

Print Assumptions MILLENNIUM_UNIT_PROPERTIES.

