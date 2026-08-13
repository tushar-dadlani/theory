(* ================================================================= *)
(*  WeylWinding.v                                                     *)
(*                                                                    *)
(*  Sharpening the zero count (ZeroCounting.v) to a WEYL-PHASE WINDING. *)
(*                                                                    *)
(*  The Weyl phase Wxi t = cayley(RtoC(xir t)) lives on the unit        *)
(*  circle and NEVER reaches +1 (Wxi_never_one) -- it lives on          *)
(*  U(1)\{1}.  Its imaginary part has the OPPOSITE sign of xir          *)
(*  (Wxi_hemisphere): xir < 0 <-> upper hemisphere (Im Wxi > 0),        *)
(*  xir > 0 <-> lower hemisphere (Im Wxi < 0), xir = 0 <-> the antipode *)
(*  -1 (Im Wxi = 0, the ONLY boundary point reached).                  *)
(*                                                                    *)
(*  So a sign change of xir is a genuine HALF-WINDING of Wxi through    *)
(*  the antipode -1 (weyl_halfwinding_up/_down): the phase moves from   *)
(*  one hemisphere, across -1, to the other.  Counting zeros =          *)
(*  counting antipode crossings = counting half-windings                *)
(*  (weyl_winding_count).                                              *)
(*                                                                    *)
(*  This is the argument-principle reading of the count: N(T) is the    *)
(*  number of times the boundary-triple Weyl phase winds past the       *)
(*  Dirichlet phase -1.                                                *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField CoherenceSingularity BerryKeatingDilation
        SelfAdjointExtension WeylFunction ZeroCounting.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  The imaginary part of the Weyl phase tracks -xir             *)
(* ----------------------------------------------------------------- *)

Lemma cayley_RtoC_Im : forall x, Im (cayley (RtoC x)) * (x * x + 1) = - (2 * x).
Proof.
  intro x. unfold cayley, Cdiv, Cmul, Cminus, Cadd, Cinv, Cnorm2, Ci, RtoC; cbn [Re Im].
  field; nra.
Qed.

Lemma Wxi_Im_num : forall t, Im (Wxi t) * (xir t * xir t + 1) = - (2 * xir t).
Proof. intro t; unfold Wxi; apply cayley_RtoC_Im. Qed.

Lemma xir_denom_pos : forall t, 0 < xir t * xir t + 1.
Proof. intro t; nra. Qed.

(* the three hemisphere equivalences *)
Lemma Wxi_Im_zero_iff : forall t, Im (Wxi t) = 0 <-> xir t = 0.
Proof.
  intro t. pose proof (Wxi_Im_num t) as HN. pose proof (xir_denom_pos t) as Hd. nra.
Qed.

Lemma Wxi_Im_pos_iff : forall t, 0 < Im (Wxi t) <-> xir t < 0.
Proof.
  intro t. pose proof (Wxi_Im_num t) as HN. pose proof (xir_denom_pos t) as Hd. nra.
Qed.

Lemma Wxi_Im_neg_iff : forall t, Im (Wxi t) < 0 <-> 0 < xir t.
Proof.
  intro t. pose proof (Wxi_Im_num t) as HN. pose proof (xir_denom_pos t) as Hd. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Wxi lives on U(1)\{1}: it never reaches the point +1         *)
(* ----------------------------------------------------------------- *)

Lemma Wxi_never_one : forall t, Wxi t <> C1.
Proof.
  intros t H.
  assert (Him : Im (Wxi t) = 0) by (rewrite H; unfold C1; reflexivity).
  apply Wxi_Im_zero_iff in Him.
  pose proof (proj1 (zeros_are_Dirichlet_phase t) (proj2 (spec_Bxi_xir t) Him)) as HD.
  rewrite H in HD. apply uDir_ne_C1; symmetry; exact HD.
Qed.

(* the antipode -1 is the ONLY boundary point Wxi reaches (Im = 0). *)
Lemma Wxi_antipode_iff : forall t, Wxi t = uDir <-> Im (Wxi t) = 0.
Proof.
  intro t; split.
  - intro H. rewrite H; unfold uDir; reflexivity.
  - intro H. apply Wxi_Im_zero_iff in H.
    apply zeros_are_Dirichlet_phase, (proj2 (spec_Bxi_xir t)); exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  A sign change is a HALF-WINDING through the antipode -1      *)
(* ----------------------------------------------------------------- *)

(* xir - to + : Wxi moves from the upper hemisphere, across -1, to the  *)
(* lower hemisphere (a clockwise half-turn through the antipode).       *)
Theorem weyl_halfwinding_up : forall a b, a < b -> xir a < 0 -> 0 < xir b ->
  exists t, a < t < b /\ Wxi t = uDir /\ 0 < Im (Wxi a) /\ Im (Wxi b) < 0.
Proof.
  intros a b Hab Ha Hb.
  destruct (sign_change_zero_up a b Hab Ha Hb) as [t [[Hta Htb] Hs]].
  exists t; repeat split.
  - exact Hta.
  - exact Htb.
  - apply zeros_are_Dirichlet_phase; exact Hs.
  - apply Wxi_Im_pos_iff; exact Ha.
  - apply Wxi_Im_neg_iff; exact Hb.
Qed.

(* xir + to - : Wxi moves from the lower hemisphere, across -1, to the  *)
(* upper hemisphere (a counter-clockwise half-turn through -1).         *)
Theorem weyl_halfwinding_down : forall a b, a < b -> 0 < xir a -> xir b < 0 ->
  exists t, a < t < b /\ Wxi t = uDir /\ Im (Wxi a) < 0 /\ 0 < Im (Wxi b).
Proof.
  intros a b Hab Ha Hb.
  destruct (sign_change_zero_down a b Hab Ha Hb) as [t [[Hta Htb] Hs]].
  exists t; repeat split.
  - exact Hta.
  - exact Htb.
  - apply zeros_are_Dirichlet_phase; exact Hs.
  - apply Wxi_Im_neg_iff; exact Ha.
  - apply Wxi_Im_pos_iff; exact Hb.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  Counting zeros = counting Weyl-phase windings through -1     *)
(* ----------------------------------------------------------------- *)

(* For a strictly increasing sample with parity-alternating signs, each *)
(* gap carries a crossing of the Dirichlet phase -1: N sign            *)
(* alternations = N half-windings of the Weyl phase through -1 = N       *)
(* zeros.  Each crossing is transversal (the hemisphere flips) and Wxi   *)
(* never touches the excluded point +1 (Wxi_never_one).                 *)
Theorem weyl_winding_count : forall (s : nat -> R) (n : nat),
  (forall i, (i < n)%nat -> s i < s (S i)) ->
  (forall i, (i <= n)%nat -> alt_sign s i) ->
  forall i, (i < n)%nat -> exists t, s i < t < s (S i) /\ Wxi t = uDir.
Proof.
  intros s n Hmono Hsign i Hi.
  destruct (alternation_zeros s n Hmono Hsign i Hi) as [t [Ht Hs]].
  exists t; split; [ exact Ht | apply zeros_are_Dirichlet_phase; exact Hs ].
Qed.

Print Assumptions Wxi_never_one.
Print Assumptions weyl_halfwinding_up.
Print Assumptions weyl_winding_count.
