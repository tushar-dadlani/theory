(* ================================================================= *)
(*  CDescription.v  --  DEFINITE DESCRIPTION inside the four-axiom     *)
(*  budget: how to turn a Prop into data without any choice axiom.     *)
(*                                                                    *)
(*  The development's standing rule is that every theorem reduces to   *)
(*  at most                                                           *)
(*    ClassicalDedekindReals.sig_not_dec, sig_forall_dec,             *)
(*    FunctionalExtensionality.functional_extensionality_dep,          *)
(*    Classical_Prop.classic.                                         *)
(*  Several files record the belief that this budget forbids producing *)
(*  a FUNCTION from a pointwise existential.  CZeroFactorDisk.v:34-40  *)
(*  says of exactly that step: "manufacturing a derivative FUNCTION    *)
(*  from a pointwise existential would need a choice axiom this        *)
(*  development does not use."  XiZeroEnum.v:9-16 says turning the     *)
(*  per-radius zero lists into a sequence "is exactly `choice`".       *)
(*                                                                    *)
(*  The first of those is not right, and this file shows why.  The     *)
(*  operative distinction is not choice versus no-choice but           *)
(*                                                                    *)
(*        CHOICE (pick one of many)  vs  DESCRIPTION (name the one).   *)
(*                                                                    *)
(*  Choice is genuinely out of budget.  Description is not, because    *)
(*  Raxioms.completeness                                              *)
(*                                                                    *)
(*    forall E : R -> Prop, bound E -> (exists x, E x) -> {m | is_lub E m}
*)
(*                                                                    *)
(*  takes an ARBITRARY Prop-valued predicate and returns a real as     *)
(*  DATA, and is itself proved from sig_forall_dec/sig_not_dec (it is  *)
(*  a Lemma, not an Axiom).  If the predicate happens to hold of       *)
(*  exactly one point, its supremum IS that point -- so any uniquely   *)
(*  determined real can be named.  Uniqueness even supplies `bound`    *)
(*  for free, so no a priori estimate is needed.                       *)
(*                                                                    *)
(*  The repo already uses completeness this way to build a whole       *)
(*  function nat -> R (LimSup.tail_lub_sig / tsup, LimSup.v:94-105,    *)
(*  and Ell2.v:592) -- the sig is uniform in the parameter, so         *)
(*  fun n => proj1_sig (...) type-checks.  Cderiv_fun below is the     *)
(*  same move at a C-valued parameter.                                 *)
(*                                                                    *)
(*  WHAT IS STILL OUT OF BUDGET, and this file does not attempt:       *)
(*  INDEFINITE description -- extracting a witness from `exists x, P x`*)
(*  when P has many solutions, over R, C, or list C.  That is choice.  *)
(*  Over nat it is affordable (sig_forall_dec; see XiTMSelect.natsel), *)
(*  but nat is special.                                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Classical_Prop.
Require Import ComplexField Cmodulus Holomorphic CDeriv CDerivUnique.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- every Prop is decidable INTO Type.                       *)
(*                                                                    *)
(*  sig_not_dec gives {~~P} + {~P} as a sumbool, i.e. in Type; classic *)
(*  (through NNPP) collapses the left branch.  This is                *)
(*  excluded_middle_informative, but obtained from the two axioms the  *)
(*  budget already contains rather than from ClassicalDescription,     *)
(*  which routes through constructive_definite_description and would   *)
(*  add an axiom.                                                      *)
(* ----------------------------------------------------------------- *)

Lemma prop_dec : forall P : Prop, {P} + {~ P}.
Proof.
  intro P.
  destruct (ClassicalDedekindReals.sig_not_dec P) as [Hnn | Hn].
  - left. apply NNPP. exact Hnn.
  - right. exact Hn.
Defined.

Print Assumptions prop_dec.

(* ----------------------------------------------------------------- *)
(*  Part B -- definite description for R.                              *)
(* ----------------------------------------------------------------- *)

Lemma R_definite_description : forall P : R -> Prop,
  (exists x, P x) -> (forall y z, P y -> P z -> y = z) -> { x | P x }.
Proof.
  intros P Hex Huniq.
  assert (Hb : bound P).
  { destruct Hex as [x Hx]. exists x. intros y Hy. right. exact (Huniq y x Hy Hx). }
  destruct (completeness P Hb Hex) as [m [Hub Hlub]].
  exists m.
  destruct Hex as [x Hx].
  assert (Hm : m = x).
  { apply Rle_antisym.
    - apply Hlub. intros y Hy. right. exact (Huniq y x Hy Hx).
    - apply Hub. exact Hx. }
  rewrite Hm. exact Hx.
Defined.

Print Assumptions R_definite_description.

(* ----------------------------------------------------------------- *)
(*  Part C -- definite description for C, componentwise.               *)
(* ----------------------------------------------------------------- *)

Lemma C_definite_description : forall P : C -> Prop,
  (exists w, P w) -> (forall y z, P y -> P z -> y = z) -> { w | P w }.
Proof.
  intros P Hex Huniq.
  assert (HRe : { x : R | exists w, P w /\ Re w = x }).
  { apply R_definite_description.
    - destruct Hex as [w Hw]. exists (Re w), w. split; [ exact Hw | reflexivity ].
    - intros y z [wy [Hwy Hy]] [wz [Hwz Hz]].
      rewrite <- Hy, <- Hz, (Huniq wy wz Hwy Hwz). reflexivity. }
  assert (HIm : { x : R | exists w, P w /\ Im w = x }).
  { apply R_definite_description.
    - destruct Hex as [w Hw]. exists (Im w), w. split; [ exact Hw | reflexivity ].
    - intros y z [wy [Hwy Hy]] [wz [Hwz Hz]].
      rewrite <- Hy, <- Hz, (Huniq wy wz Hwy Hwz). reflexivity. }
  destruct HRe as [x Hx]. destruct HIm as [y Hy].
  exists (mkC x y).
  destruct Hx as [wx [Hwx Hxe]]. destruct Hy as [wy [Hwy Hye]].
  assert (Hwe : wy = wx) by exact (Huniq wy wx Hwy Hwx).
  subst wy. subst x. subst y.
  replace (mkC (Re wx) (Im wx)) with wx by (destruct wx; reflexivity).
  exact Hwx.
Defined.

Print Assumptions C_definite_description.

(* ----------------------------------------------------------------- *)
(*  Part D -- the payload: a derivative FUNCTION from pointwise        *)
(*  existence.  Holomorphy is stated existentially throughout the      *)
(*  development (disk_holo F R2 = forall z, Cmod z < R2 -> exists d,   *)
(*  is_Cderiv F z d), and CDerivGlobal's Fderiv/ptcont apparatus       *)
(*  exists to work around the belief that the existential cannot be    *)
(*  Skolemised.  It can: derivatives are UNIQUE                        *)
(*  (CDerivUnique.is_Cderiv_unique), so this is description, not       *)
(*  choice, and the sig is uniform in z so it lambda-abstracts.        *)
(* ----------------------------------------------------------------- *)

Definition Cderiv_sig (F : C -> C) (H : forall z, exists d, is_Cderiv F z d)
  : forall z, { d | is_Cderiv F z d }.
Proof.
  intro z. apply C_definite_description.
  - exact (H z).
  - intros y w Hy Hw. exact (is_Cderiv_unique F z y w Hy Hw).
Defined.

Definition Cderiv_fun (F : C -> C) (H : forall z, exists d, is_Cderiv F z d) : C -> C :=
  fun z => proj1_sig (Cderiv_sig F H z).

Theorem Cderiv_fun_spec : forall F H z, is_Cderiv F z (Cderiv_fun F H z).
Proof. intros F H z. unfold Cderiv_fun. exact (proj2_sig (Cderiv_sig F H z)). Qed.

Print Assumptions Cderiv_fun_spec.

(* ----------------------------------------------------------------- *)
(*  Part E -- sanity check.  The described derivative of z*z really is *)
(*  z + z, recovered by uniqueness.                                    *)
(* ----------------------------------------------------------------- *)

Lemma sq_deriv : forall z, is_Cderiv (fun w => Cmul w w) z (Cadd z z).
Proof.
  intro z.
  replace (Cadd z z) with (Cadd (Cmul C1 z) (Cmul z C1)) by ring.
  apply (Cderiv_mul (fun w => w) (fun w => w) z C1 C1); apply Cderiv_id.
Qed.

Lemma sq_holo : forall z, exists d, is_Cderiv (fun w => Cmul w w) z d.
Proof. intro z. exists (Cadd z z). apply sq_deriv. Qed.

Example Cderiv_fun_on_sq :
  forall z, Cderiv_fun (fun w => Cmul w w) sq_holo z = Cadd z z.
Proof.
  intro z.
  exact (is_Cderiv_unique _ z _ _ (Cderiv_fun_spec _ sq_holo z) (sq_deriv z)).
Qed.

Print Assumptions Cderiv_fun_on_sq.

(* ================================================================= *)
(*  END CDescription.v                                                *)
(* ================================================================= *)
