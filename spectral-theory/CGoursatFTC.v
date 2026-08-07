(* ================================================================= *)
(*  CGoursatFTC.v  —  Milestone C, brick C2a-3a: the segment FTC and     *)
(*  "a function with a primitive has zero triangle integral".           *)
(*                                                                    *)
(*  seg_FTC : seg_int f a b = H b − H a  for a primitive H of f, via     *)
(*  CPathFTC.pathint_FTC on the straight-line path.  Telescoping over    *)
(*  the three edges gives tri_int_primitive_zero : tri_int f = 0 when f  *)
(*  has a global primitive.  Applied to the affine part of a holomorphic *)
(*  h at the Goursat limit point, this kills it, leaving the remainder.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CIntegral2 CPathIntegral
        CPathFTC CSegInt CTriangle.
Open Scope R_scope.

(* ---- derivability of the straight-segment components ---- *)
Lemma dseg_Re : forall a b s0,
  derivable_pt_lim (fun s => Re (seg a b s)) s0 (Re (seg' a b s0)).
Proof.
  intros a b s0.
  assert (Hf : (fun s => Re (seg a b s)) = (fun s => (Re b - Re a) * s + Re a))
    by (apply functional_extensionality; intro s;
        unfold seg, Cadd, Cmul, RtoC, Cminus; cbn; ring).
  rewrite Hf.
  replace (Re (seg' a b s0)) with (Re b - Re a)
    by (unfold seg', Cminus; cbn; ring).
  apply dlin.
Qed.

Lemma dseg_Im : forall a b s0,
  derivable_pt_lim (fun s => Im (seg a b s)) s0 (Im (seg' a b s0)).
Proof.
  intros a b s0.
  assert (Hf : (fun s => Im (seg a b s)) = (fun s => (Im b - Im a) * s + Im a))
    by (apply functional_extensionality; intro s;
        unfold seg, Cadd, Cmul, RtoC, Cminus; cbn; ring).
  rewrite Hf.
  replace (Im (seg' a b s0)) with (Im b - Im a)
    by (unfold seg', Cminus; cbn; ring).
  apply dlin.
Qed.

(* ---- the segment fundamental theorem of calculus ---- *)
Lemma seg_FTC : forall (H f : C -> C) (Hf : CcontC f) a b,
  (forall z, is_Cderiv H z (f z)) ->
  seg_int f Hf a b = Cminus (H b) (H a).
Proof.
  intros H f Hf a b HH; unfold seg_int.
  transitivity (Cminus (H (seg a b 1)) (H (seg a b 0))).
  - exact (pathint_FTC H f (seg a b) (seg' a b) (seg_ig_cont f Hf a b) 0 1 ltac:(lra)
            (fun s _ => HH (seg a b s))
            (fun s _ => dseg_Re a b s)
            (fun s _ => dseg_Im a b s)).
  - rewrite seg_1, seg_0; reflexivity.
Qed.

(* ---- a function with a primitive integrates to 0 over any triangle ---- *)
Theorem tri_int_primitive_zero : forall (H f : C -> C) (Hf : CcontC f) v0 v1 v2,
  (forall z, is_Cderiv H z (f z)) ->
  tri_int f Hf v0 v1 v2 = C0.
Proof.
  intros H f Hf v0 v1 v2 HH; unfold tri_int.
  rewrite (seg_FTC H f Hf v0 v1 HH), (seg_FTC H f Hf v1 v2 HH),
          (seg_FTC H f Hf v2 v0 HH); ring.
Qed.

Print Assumptions tri_int_primitive_zero.

(* ================================================================= *)
(*  END CGoursatFTC.v  —  segment FTC + triangle-primitive-zero.        *)
(* ================================================================= *)
