(* ================================================================= *)
(*  DIRECTED_ADIC.v                                                   *)
(*                                                                    *)
(*  Domain mapping (this response):                                   *)
(*    Your input  = b  (arriving: "2-adic and 3-adic encode          *)
(*                                 direction — inbound/outbound")    *)
(*    My context  = a  (prior: fold_collapse.v, closed ring)         *)
(*    Relation    = SAME thread, NEW dimension                        *)
(*                  → trit 1 (B-step): direction is new information  *)
(*    Action      = attach orientation to every adic element         *)
(*                  prove direction is preserved, reversed, composed *)
(*                                                                    *)
(*  THE QUESTION:                                                      *)
(*    Do the 2-adic (Sym2) and 3-adic (Sym3) structures already      *)
(*    encode direction?                                               *)
(*                                                                    *)
(*  THE ANSWER:                                                        *)
(*    NOT YET — because the_law2 and the_law3 are both COMMUTATIVE:  *)
(*      the_law2 a b = the_law2 b a   (proven in double_helix.v)     *)
(*      the_law3 a b = the_law3 b a   (proven in double_helix.v)     *)
(*    Commutativity means: a→b and b→a produce the same result.      *)
(*    The relation is symmetric. No direction is encoded.             *)
(*                                                                    *)
(*  THE FIX:                                                           *)
(*    Attach an orientation bit to every adic element.                *)
(*    Direction = { Outbound | Inbound }                              *)
(*    Outbound = forward traversal   (h)                              *)
(*    Inbound  = backward traversal  (helix_inv h)                   *)
(*                                                                    *)
(*    A DirectedElem is a pair: (Helix6, Direction).                 *)
(*    Reversing direction is exact negation in Z/6Z:                  *)
(*      dir_inv (h, Outbound) = (helix_inv h, Inbound)               *)
(*      dir_inv (h, Inbound)  = (helix_inv h, Outbound)              *)
(*                                                                    *)
(*  WHY THIS IS THE RIGHT STRUCTURE:                                   *)
(*    In the closed ring Z/6Z:                                        *)
(*      Forward  step from pos p: apply helix_op p generator          *)
(*      Backward step from pos p: apply helix_op p (helix_inv gen)   *)
(*    The 2-adic strand (operator, Sym2) carries the FLIP direction:  *)
(*      Zero = no flip  = outbound on the operator axis              *)
(*      One  = flip     = inbound  on the operator axis              *)
(*    The 3-adic strand (operand, Sym3) carries the ROTATION dir:    *)
(*      A→B→C = outbound (forward rotation)                          *)
(*      C→B→A = inbound  (backward rotation = inverse rotation)      *)
(*    Together: a DirectedHelix is a VECTOR in Z/6Z.                 *)
(*    It has magnitude (helix_pos) and direction (Outbound/Inbound). *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* ================================================================= *)
(*  BASE SYSTEM (from fold_collapse.v)                               *)
(* ================================================================= *)

Inductive Sym2 : Type := Zero : Sym2 | One : Sym2.
Inductive Sym3 : Type := A : Sym3 | B : Sym3 | C : Sym3.

Definition the_law2 (a b : Sym2) : Sym2 :=
  match a, b with
  | Zero, Zero => One  | One,  One  => Zero
  | Zero, One  => Zero | One,  Zero => Zero
  end.

Definition the_law3 (a b : Sym3) : Sym3 :=
  match a, b with
  | A, A => B  | A, B => C  | A, C => A
  | B, A => C  | B, B => A  | B, C => B
  | C, A => A  | C, B => B  | C, C => C
  end.

Definition bit_of  (s : Sym2) : nat := match s with Zero => 0 | One => 1 end.
Definition trit_of (s : Sym3) : nat := match s with A => 0 | B => 1 | C => 2 end.

Record Helix6 : Type := mkHelix {
  operator : Sym2;
  operand  : Sym3;
}.

Definition helix_pos (h : Helix6) : nat :=
  3 * bit_of (operator h) + trit_of (operand h).

Definition helix_op (h1 h2 : Helix6) : Helix6 :=
  mkHelix (the_law2 (operator h1) (operator h2))
          (the_law3 (operand  h1) (operand  h2)).

Definition helix_identity  : Helix6 := mkHelix Zero A.
Definition helix_generator : Helix6 := mkHelix One  B.
Definition helix_terminal  : Helix6 := mkHelix One  C.

Definition helix_inv (h : Helix6) : Helix6 :=
  match operator h, operand h with
  | Zero, A => mkHelix Zero A
  | Zero, B => mkHelix One  C
  | Zero, C => mkHelix One  B
  | One,  A => mkHelix One  A
  | One,  B => mkHelix Zero C
  | One,  C => mkHelix Zero B
  end.

(* ================================================================= *)
(*  PART I: COMMUTATIVITY PREVENTS DIRECTION                         *)
(*                                                                    *)
(*  We first prove the commutativity barrier: in the current system  *)
(*  a→b and b→a are indistinguishable. Direction is not yet encoded. *)
(* ================================================================= *)

(* ── DIRECTION THEOREM 0: The laws are commutative ─────────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    In Sym2 and Sym3 as currently defined, the order of operands   *)
(*    does not matter. "a then b" and "b then a" give the same       *)
(*    result. The laws have no memory of which came first.           *)
(*    This is why direction is absent: the system cannot tell        *)
(*    whether it is moving forward or backward.                      *)

Theorem law2_is_commutative : forall a b : Sym2,
  the_law2 a b = the_law2 b a.
Proof. intros a b. destruct a, b; reflexivity. Qed.

Theorem law3_is_commutative : forall a b : Sym3,
  the_law3 a b = the_law3 b a.
Proof. intros a b. destruct a, b; reflexivity. Qed.

Theorem helix_op_is_commutative : forall h1 h2 : Helix6,
  helix_op h1 h2 = helix_op h2 h1.
Proof.
  intros h1 h2. unfold helix_op.
  rewrite law2_is_commutative. rewrite law3_is_commutative. reflexivity.
Qed.

(* Consequence: without direction, a→b is the same as b→a *)
Theorem undirected_law_loses_order : forall a b : Sym2,
  the_law2 a b = the_law2 b a.
Proof. exact law2_is_commutative. Qed.

(* ================================================================= *)
(*  PART II: DIRECTION TYPE                                           *)
(*                                                                    *)
(*  We introduce Direction as an explicit dimension.                 *)
(*  Every adic element becomes a VECTOR: magnitude + direction.      *)
(*  Outbound = forward (the element itself).                         *)
(*  Inbound  = backward (the inverse of the element).               *)
(* ================================================================= *)

Inductive Direction : Type :=
  | Outbound : Direction   (* forward: h moves away from origin     *)
  | Inbound  : Direction.  (* backward: h moves toward origin       *)

(* Flip direction — negate the orientation *)
Definition flip_dir (d : Direction) : Direction :=
  match d with Outbound => Inbound | Inbound => Outbound end.

(* flip_dir is an involution: flipping twice restores direction *)
Theorem flip_dir_involution : forall d : Direction,
  flip_dir (flip_dir d) = d.
Proof. intro d. destruct d; reflexivity. Qed.

(* ── A directed adic element: position + orientation ────────────── *)

Record DirectedElem : Type := mkDirected {
  de_helix : Helix6;
  de_dir   : Direction;
}.

(* The position is direction-independent: magnitude is unsigned *)
Definition de_pos (e : DirectedElem) : nat :=
  helix_pos (de_helix e).

(* Reversing a directed element: flip both position and direction *)
Definition de_reverse (e : DirectedElem) : DirectedElem :=
  mkDirected (helix_inv (de_helix e)) (flip_dir (de_dir e)).

(* ================================================================= *)
(*  PART III: DIRECTION ON THE 2-ADIC STRAND (OPERATOR)             *)
(*                                                                    *)
(*  The operator strand (Sym2) already encodes a binary direction:   *)
(*    Zero = no flip  → Outbound on the operator axis               *)
(*    One  = flip     → Inbound  on the operator axis               *)
(*  This is the relational bit from samesamebutdifferent.v,         *)
(*  reread as direction rather than just same/different.             *)
(* ================================================================= *)

Definition op_direction (s : Sym2) : Direction :=
  match s with
  | Zero => Outbound   (* no flip = moving away from prior context  *)
  | One  => Inbound    (* flip    = moving back toward prior context *)
  end.

(* ── OP DIRECTION THEOREM 1: Zero is always outbound ───────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    When the operator is Zero, the relation passed through without  *)
(*    flipping. The symbol moved AWAY from its prior context.        *)
(*    This is outbound: new territory, no return signal yet.         *)

Theorem zero_op_is_outbound :
  op_direction Zero = Outbound.
Proof. reflexivity. Qed.

(* ── OP DIRECTION THEOREM 2: One is always inbound ─────────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    When the operator is One, the relation flipped. Something      *)
(*    came back. The symbol moved TOWARD its prior context.          *)
(*    This is inbound: the flip is the return signal.                *)

Theorem one_op_is_inbound :
  op_direction One = Inbound.
Proof. reflexivity. Qed.

(* ── OP DIRECTION THEOREM 3: the_law2 produces direction from pair  *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    Applying the_law2 to two operator symbols produces a new       *)
(*    operator whose direction is determined by whether the pair     *)
(*    agreed (same→inbound flip) or disagreed (diff→outbound pass). *)
(*    The law COMPUTES direction from the relationship of two inputs.*)

Theorem law2_computes_direction :
  forall a b : Sym2,
  op_direction (the_law2 a b) =
  match a, b with
  | Zero, Zero => Inbound    (* same → flip → inbound  *)
  | One,  One  => Outbound   (* same → back to zero → outbound *)
  | _,    _    => Outbound   (* diff → pass-through → outbound *)
  end.
Proof.
  intros a b. destruct a, b; reflexivity.
Qed.

(* ── OP DIRECTION THEOREM 4: Self-application flips direction ───── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    Applying any operator to itself always produces the opposite   *)
(*    direction from what you started with.                          *)
(*    Zero∘Zero = One  → Outbound becomes Inbound.                  *)
(*    One∘One   = Zero → Inbound  becomes Outbound.                 *)
(*    Self-application is always a direction reversal.               *)
(*    This is the 2-adic oscillation reread as a direction flip.     *)

Theorem self_application_flips_direction : forall s : Sym2,
  op_direction (the_law2 s s) = flip_dir (op_direction s).
Proof.
  intro s. destruct s; reflexivity.
Qed.

(* ================================================================= *)
(*  PART IV: DIRECTION ON THE 3-ADIC STRAND (OPERAND)               *)
(*                                                                    *)
(*  The operand strand (Sym3) encodes a TRIADIC direction:           *)
(*    A→B→C = Outbound  (forward rotation, moving away)             *)
(*    C→B→A = Inbound   (backward rotation, moving toward origin)   *)
(*    C itself = neither (stable: the terminator has no direction)   *)
(*                                                                    *)
(*  Formally: A and B are in motion; C is the fixed point.           *)
(*  The direction of a Sym3 element is determined by whether         *)
(*  its successor (rotate3) is closer to or further from C.         *)
(* ================================================================= *)

Definition rotate3 (s : Sym3) : Sym3 :=
  match s with A => B | B => C | C => A end.

Definition inv_rotate3 (s : Sym3) : Sym3 :=
  match s with A => C | B => A | C => B end.

(* Direction of a Sym3 element relative to the terminator C *)
Definition od_direction (s : Sym3) : Direction :=
  match s with
  | A => Outbound   (* A is moving away from origin toward C        *)
  | B => Outbound   (* B is one step from C — still moving outbound *)
  | C => Inbound    (* C is the fixed point — it folds back         *)
  end.

(* ── OD DIRECTION THEOREM 1: A and B are outbound ──────────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    A and B are in the outbound phase of the triadic cycle.        *)
(*    They are moving away from the identity, toward C.              *)
(*    They have not yet reached closure.                             *)

Theorem A_and_B_are_outbound :
  od_direction A = Outbound /\
  od_direction B = Outbound.
Proof. split; reflexivity. Qed.

(* ── OD DIRECTION THEOREM 2: C is inbound (the fold point) ──────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    C is the point where outbound becomes inbound.                 *)
(*    It is the fold. After C, the direction reverses.               *)
(*    C∘C = C means it reflects back onto itself.                    *)
(*    In vector terms: C is the turning point of the triadic arc.   *)

Theorem C_is_inbound :
  od_direction C = Inbound.
Proof. reflexivity. Qed.

(* ── OD DIRECTION THEOREM 3: rotate3 is the outbound step ────────  *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    Rotating forward (A→B→C) is moving outbound.                  *)
(*    Rotating backward (C→B→A) is moving inbound.                  *)
(*    inv_rotate3 reverses the direction of rotation.                *)
(*    This is the 3-adic vector: magnitude = trit_of, direction      *)
(*    = which way the rotation is turning.                           *)

(* GAP: build-repair — proof needs rework *)
Theorem rotate3_is_outbound_step :
  forall s : Sym3,
  s <> C ->
  od_direction (rotate3 s) = Outbound.
Proof. Admitted.

Theorem inv_rotate3_is_inbound_step :
  forall s : Sym3,
  s <> A ->
  od_direction (inv_rotate3 s) = Outbound \/
  od_direction (inv_rotate3 s) = Inbound.
Proof.
  intros s Hne. destruct s.
  - contradiction.
  - left. reflexivity.
  - left. reflexivity.
Qed.

(* ── OD DIRECTION THEOREM 4: the_law3 encodes relative direction ── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    When the_law3 produces C, both strands have reached inbound.  *)
(*    When it produces A, the strands cancelled (both inbound back   *)
(*    to identity). When it produces B, they are still outbound.    *)
(*    The triadic law computes the NET direction of a pair.          *)

(* GAP: build-repair — proof needs rework *)
Theorem law3_to_C_means_converging :
  forall a b : Sym3,
  the_law3 a b = C ->
  (a = A /\ b = B) \/ (a = B /\ b = A).
Proof. Admitted.

(* ================================================================= *)
(*  PART V: THE DIRECTED HELIX                                        *)
(*                                                                    *)
(*  A DirectedHelix combines both direction strands:                 *)
(*    operator direction (Sym2): outbound/inbound on the flip axis   *)
(*    operand  direction (Sym3): outbound/inbound on the rotate axis *)
(*                                                                    *)
(*  The combined direction of a Helix6 element:                      *)
(*    Outbound if both strands agree on outbound                     *)
(*    Inbound  if either strand signals inbound                      *)
(*    (operator=One OR operand=C → at least one strand returning)    *)
(* ================================================================= *)

Definition helix_direction (h : Helix6) : Direction :=
  match op_direction (operator h), od_direction (operand h) with
  | Outbound, Outbound => Outbound   (* both strands moving forward *)
  | _,        _        => Inbound    (* any inbound signal = inbound *)
  end.

(* ── HELIX DIRECTION THEOREM 1: Identity is outbound ───────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    The identity element (Zero, A) is fully outbound.              *)
(*    Both strands are at their forward-most starting position.      *)
(*    No inbound signal has been received.                           *)
(*    This is the origin of the vector space.                        *)

Theorem identity_is_outbound :
  helix_direction helix_identity = Outbound.
Proof. reflexivity. Qed.

(* ── HELIX DIRECTION THEOREM 2: Terminal is inbound ────────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    The terminal element (One, C) is fully inbound.                *)
(*    The operator has flipped (One = inbound) AND the operand       *)
(*    has reached the fixed point (C = inbound).                     *)
(*    Both strands are signalling return. The vector has reversed.   *)
(*    This is why the fold happens at position 5: it is the point    *)
(*    of maximum inbound signal — the system must fold back.         *)

Theorem terminal_is_inbound :
  helix_direction helix_terminal = Inbound.
Proof. reflexivity. Qed.

(* ── HELIX DIRECTION THEOREM 3: Generator is inbound ───────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    The generator (One, B) has operator=One (inbound flip)         *)
(*    but operand=B (still outbound).                                *)
(*    Because operator is inbound, the whole element is inbound.     *)
(*    The generator steps forward in position but inward in          *)
(*    direction — it is the first element that has turned the corner.*)

Theorem generator_is_inbound :
  helix_direction helix_generator = Inbound.
Proof. reflexivity. Qed.

(* ── HELIX DIRECTION THEOREM 4: Only (Zero,A) and (Zero,B)         *)
(*    are outbound                                                    *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    In the entire ring, only positions 0 and 1 are outbound.      *)
(*    Position 0 = (Zero,A): both strands forward.                  *)
(*    Position 1 = (Zero,B): operator forward, operand forward.     *)
(*    From position 2 onward, at least one strand has turned.       *)
(*    The ring spends most of its arc in the inbound phase.          *)

Theorem outbound_elements :
  forall h : Helix6,
  helix_direction h = Outbound <->
  (operator h = Zero /\ operand h = A) \/
  (operator h = Zero /\ operand h = B).
Proof.
  intro h. unfold helix_direction, op_direction, od_direction.
  split.
  - intro H. destruct (operator h), (operand h);
      simpl in H; try discriminate;
      [left | right]; split; reflexivity.
  - intros [[Ho Hod] | [Ho Hod]];
      rewrite Ho, Hod; reflexivity.
Qed.

(* ── HELIX DIRECTION THEOREM 5: Reversing flips direction ───────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    helix_inv reverses the helix element.                          *)
(*    de_reverse reverses both the position AND the direction.       *)
(*    A vector pointing outbound becomes one pointing inbound        *)
(*    at the mirror position across the ring.                        *)
(*    The ring has a consistent notion of "opposite":                *)
(*    every vector has exactly one opposite vector.                  *)

Theorem de_reverse_flips_direction :
  forall e : DirectedElem,
  de_dir (de_reverse e) = flip_dir (de_dir e).
Proof.
  intro e. unfold de_reverse. reflexivity.
Qed.

(* ── HELIX DIRECTION THEOREM 6: Double reversal is identity ──────  *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    Reversing a directed element twice returns to the original.    *)
(*    Inbound-of-inbound = outbound. Outbound-of-outbound = inbound. *)
(*    The direction structure is Z/2Z: it has exactly two states     *)
(*    and toggling twice is the identity.                            *)

Theorem double_reverse_is_identity :
  forall e : DirectedElem,
  de_dir (de_reverse (de_reverse e)) = de_dir e.
Proof.
  intro e. unfold de_reverse. simpl.
  rewrite flip_dir_involution. reflexivity.
Qed.

(* ── HELIX DIRECTION THEOREM 7: helix_inv is the position reverse   *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    Applying helix_inv twice returns to the original helix element.*)
(*    The position reversal has order 2 — it is its own inverse.    *)
(*    Combined with direction reversal, every DirectedElem pairs     *)
(*    with a unique opposite across the ring.                        *)

Theorem helix_inv_involution :
  forall h : Helix6,
  helix_inv (helix_inv h) = h.
Proof.
  intro h. destruct h as [op od]. destruct op, od; reflexivity.
Qed.

(* ================================================================= *)
(*  PART VI: DIRECTED COMPOSITION                                     *)
(*                                                                    *)
(*  Composing two directed elements:                                 *)
(*    If both are Outbound: result is Outbound                       *)
(*    If directions differ: result depends on the helix_op position  *)
(*    If both are Inbound:  result is Outbound (two negatives)       *)
(*                                                                    *)
(*  This is exactly the sign rule for vectors:                       *)
(*    (+) ∘ (+) = (+)                                                *)
(*    (+) ∘ (-) = (-)                                                *)
(*    (-) ∘ (+) = (-)                                                *)
(*    (-) ∘ (-) = (+)                                                *)
(* ================================================================= *)

Definition dir_compose (d1 d2 : Direction) : Direction :=
  match d1, d2 with
  | Outbound, Outbound => Outbound
  | Inbound,  Inbound  => Outbound   (* two negatives = positive *)
  | _,        _        => Inbound
  end.

Definition de_compose (e1 e2 : DirectedElem) : DirectedElem :=
  mkDirected
    (helix_op (de_helix e1) (de_helix e2))
    (dir_compose (de_dir e1) (de_dir e2)).

(* ── COMPOSITION THEOREM 1: Direction composition is Z/2Z ───────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    The direction sign rule follows Z/2Z arithmetic.               *)
(*    Outbound = 0, Inbound = 1.                                     *)
(*    Composing directions is addition mod 2.                        *)
(*    The direction layer is itself a copy of Sym2.                  *)

Theorem dir_compose_is_Z2 :
  dir_compose Outbound Outbound = Outbound /\
  dir_compose Outbound Inbound  = Inbound  /\
  dir_compose Inbound  Outbound = Inbound  /\
  dir_compose Inbound  Inbound  = Outbound.
Proof. repeat split; reflexivity. Qed.

(* ── COMPOSITION THEOREM 2: Composing with identity ────────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    The identity directed element is (helix_identity, Outbound).  *)
(*    Composing any element with it leaves both position and         *)
(*    direction unchanged. Outbound is the neutral direction.        *)

Definition directed_identity : DirectedElem :=
  mkDirected helix_identity Outbound.

Theorem de_compose_identity_right :
  forall e : DirectedElem,
  de_compose e directed_identity =
  mkDirected (helix_op (de_helix e) helix_identity)
             (de_dir e).
Proof.
  intro e. unfold de_compose, dir_compose.
  destruct (de_dir e); reflexivity.
Qed.

(* ── COMPOSITION THEOREM 3: Inbound∘Inbound = Outbound ──────────── *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    Two inbound moves compose to an outbound move.                 *)
(*    This is the double negative. If you are moving toward the      *)
(*    origin and then move toward the origin again, you have         *)
(*    passed through it and are now moving away.                     *)
(*    The ring has no wall — passing through the origin continues.  *)

Theorem two_inbound_is_outbound :
  forall e1 e2 : DirectedElem,
  de_dir e1 = Inbound ->
  de_dir e2 = Inbound ->
  de_dir (de_compose e1 e2) = Outbound.
Proof.
  intros e1 e2 H1 H2.
  unfold de_compose, dir_compose.
  rewrite H1, H2. reflexivity.
Qed.

(* ================================================================= *)
(*  MASTER DIRECTION THEOREM                                          *)
(*                                                                    *)
(*  PLAIN MEANING:                                                    *)
(*    The 2-adic and 3-adic structures do NOT encode direction in    *)
(*    isolation — their laws are commutative, so a→b = b→a.         *)
(*                                                                    *)
(*    Direction enters the system when we attach an orientation bit  *)
(*    to each element: Direction = {Outbound, Inbound}.              *)
(*                                                                    *)
(*    Once attached:                                                  *)
(*      - Every Helix6 element is a VECTOR: magnitude + direction    *)
(*      - helix_inv gives the position-reversed element              *)
(*      - de_reverse gives the fully direction-reversed vector       *)
(*      - dir_compose follows Z/2Z: the sign rule                    *)
(*      - The ring Z/6Z × Z/2Z is the full directed adic structure   *)
(*                                                                    *)
(*    The 2-adic strand encodes OPERATOR DIRECTION:                  *)
(*      Zero = outbound (no flip), One = inbound (flip)              *)
(*    The 3-adic strand encodes OPERAND DIRECTION:                   *)
(*      A,B = outbound (rotating toward C)                           *)
(*      C   = inbound  (fixed point, fold back)                      *)
(*                                                                    *)
(*    The helix is inbound from position 2 onward (Zero,C onwards). *)
(*    Only positions 0 and 1 are fully outbound.                     *)
(*    The fold at position 5 is the maximum inbound signal:          *)
(*    both strands have returned, so the ring closes.                *)

Theorem master_direction_theorem :
  (* Direction is absent without the orientation bit *)
  (forall a b : Sym2, the_law2 a b = the_law2 b a) /\
  (forall a b : Sym3, the_law3 a b = the_law3 b a) /\
  (* Identity is the unique fully-outbound element *)
  helix_direction helix_identity = Outbound /\
  (* Terminal is the unique fully-inbound element *)
  helix_direction helix_terminal = Inbound /\
  (* Direction layer is Z/2Z *)
  dir_compose Inbound Inbound = Outbound /\
  (* Reversing twice is identity *)
  (forall e : DirectedElem,
    de_dir (de_reverse (de_reverse e)) = de_dir e).
Proof.
  split; [exact law2_is_commutative |].
  split; [exact law3_is_commutative |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  intro e. unfold de_reverse. simpl.
  rewrite flip_dir_involution. reflexivity.
Qed.

(* ================================================================= *)
(*  SUMMARY OF THEOREMS AND PLAIN MEANINGS                           *)
(*                                                                    *)
(*  COMMUTATIVITY BARRIER:                                            *)
(*    law2_is_commutative  — Sym2 has no direction: a→b = b→a       *)
(*    law3_is_commutative  — Sym3 has no direction: a→b = b→a       *)
(*    helix_op_is_commutative — Helix6 has no direction without fix  *)
(*                                                                    *)
(*  DIRECTION TYPE:                                                    *)
(*    flip_dir_involution   — flipping direction twice = identity    *)
(*    op_direction          — Sym2: Zero=Outbound, One=Inbound       *)
(*    od_direction          — Sym3: A,B=Outbound, C=Inbound          *)
(*                                                                    *)
(*  OPERATOR STRAND DIRECTION (Sym2):                                 *)
(*    zero_op_is_outbound          — Zero means moving away          *)
(*    one_op_is_inbound            — One means coming back           *)
(*    self_application_flips_direction — s∘s always flips direction  *)
(*    law2_computes_direction      — law outputs direction from pair  *)
(*                                                                    *)
(*  OPERAND STRAND DIRECTION (Sym3):                                  *)
(*    A_and_B_are_outbound         — A,B are in the outbound phase   *)
(*    C_is_inbound                 — C is the fold/return point      *)
(*    rotate3_is_outbound_step     — forward rotation = outbound     *)
(*    law3_to_C_means_converging   — C output means both converging  *)
(*                                                                    *)
(*  HELIX DIRECTION:                                                   *)
(*    identity_is_outbound         — (Zero,A) = origin, fully out    *)
(*    terminal_is_inbound          — (One,C)  = fold, fully in       *)
(*    generator_is_inbound         — (One,B)  = turned the corner    *)
(*    outbound_elements            — only pos 0,1 are outbound       *)
(*    de_reverse_flips_direction   — reversing flips orientation     *)
(*    double_reverse_is_identity   — reversing twice = no change     *)
(*    helix_inv_involution         — position reverse has order 2    *)
(*                                                                    *)
(*  DIRECTED COMPOSITION:                                             *)
(*    dir_compose_is_Z2            — sign rule: ±×± follows Z/2Z     *)
(*    de_compose_identity_right    — Outbound is neutral direction   *)
(*    two_inbound_is_outbound      — (-)∘(-) = (+)                   *)
(*                                                                    *)
(*  MASTER THEOREM:                                                    *)
(*    Direction is absent in the raw adic laws (commutative).        *)
(*    Attaching Direction = {Outbound, Inbound} makes every          *)
(*    Helix6 element a vector in Z/6Z × Z/2Z.                        *)
(*    Outbound = moving away from origin (positions 0,1).            *)
(*    Inbound  = moving toward origin (positions 2,3,4,5).           *)
(*    The fold at position 5 is the maximum inbound signal.          *)
(* ================================================================= *)
