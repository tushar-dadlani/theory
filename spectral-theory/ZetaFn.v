(* ================================================================= *)
(*  ZetaFn.v  —  Milestone B, brick B2: zeta as a total C -> C function. *)
(*                                                                    *)
(*  zetaC s H0 H1 is a DEPENDENT function (it carries the domain        *)
(*  proofs H0 : 0<Re s and H1 : s<>1), so the holomorphy calculus       *)
(*  (is_Cderiv on C -> C maps) cannot wrap it.  Here we package a plain  *)
(*  total function zF : C -> C that agrees with zetaC on the domain     *)
(*  inDom := 0<Re s /\ s<>1 (and is 0 elsewhere), prove the value is     *)
(*  proof-irrelevant (limit uniqueness), and lift zetaC_holo to the     *)
(*  clean statement  HolomorphicOn zF inDom.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CDeriv Holomorphic
        CZeta CZetaHolo CZetaTerm.
Open Scope R_scope.

(* ---- decidable complex equality (classical, via components) ---- *)
Lemma Ceq_dec2 : forall a b : C, {a = b} + {a <> b}.
Proof.
  intros a b; destruct (Req_EM_T (Re a) (Re b)) as [Hr | Hr].
  - destruct (Req_EM_T (Im a) (Im b)) as [Hi | Hi].
    + left; apply Ceq; assumption.
    + right; intro H; apply Hi; rewrite H; reflexivity.
  - right; intro H; apply Hr; rewrite H; reflexivity.
Qed.

(* ---- the domain and the total wrapper ---- *)
Definition inDom (s : C) : Prop := 0 < Re s /\ Cminus C1 s <> C0.

Definition zF (s : C) : C :=
  match Rlt_dec 0 (Re s) with
  | left h0 => match Ceq_dec2 (Cminus C1 s) C0 with
               | left _ => C0
               | right h1 => zetaC s h0 h1
               end
  | right _ => C0
  end.

(* ---- the value of zetaC does not depend on the domain proofs ---- *)
Lemma zetaC_irrel : forall s H0 H1 H0' H1', zetaC s H0 H1 = zetaC s H0' H1'.
Proof.
  intros s H0 H1 H0' H1'; unfold zetaC; f_equal.
  apply (CUn_cv_unique (Cpsum (gtermC s)));
    [ exact (zetaC_series_cv s H0 H1) | exact (zetaC_series_cv s H0' H1') ].
Qed.

(* ---- zF agrees with zetaC on the domain ---- *)
Lemma zF_eq : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0), zF s = zetaC s H0 H1.
Proof.
  intros s H0 H1; unfold zF.
  destruct (Rlt_dec 0 (Re s)) as [h0 | h0]; [ | exfalso; lra ].
  destruct (Ceq_dec2 (Cminus C1 s) C0) as [Hc | h1];
    [ exfalso; apply H1; exact Hc | apply zetaC_irrel ].
Qed.

(* ---- zetaC_holo, lifted to the total function zF ---- *)
Theorem zF_holo : forall z, inDom z -> exists d, is_Cderiv zF z d.
Proof.
  intros z [H0 H1]; destruct (zetaC_holo z H0 H1) as [D HD].
  exists D; intros eps Heps; destruct (HD eps Heps) as [del [Hdel Hb]].
  assert (Hcm : 0 < Cmod (Cminus C1 z)) by (apply Cmod_pos_ne0; exact H1).
  set (r := Rmin del (Rmin (Re z) (Cmod (Cminus C1 z)))).
  assert (Hr : 0 < r)
    by (unfold r; repeat apply Rmin_glb_lt; [ exact Hdel | exact H0 | exact Hcm ]).
  exists r; split; [ exact Hr | ].
  intros h Hh.
  assert (Hhdel : Cmod h < del)
    by (eapply Rlt_le_trans; [ exact Hh | unfold r; apply Rmin_l ]).
  assert (HhRe : Cmod h < Re z)
    by (eapply Rlt_le_trans; [ exact Hh | unfold r; eapply Rle_trans;
          [ apply Rmin_r | apply Rmin_l ] ]).
  assert (Hhc : Cmod h < Cmod (Cminus C1 z))
    by (eapply Rlt_le_trans; [ exact Hh | unfold r; eapply Rle_trans;
          [ apply Rmin_r | apply Rmin_r ] ]).
  assert (K0 : 0 < Re (Cadd z h)).
  { unfold Cadd; cbn [Re]; pose proof (Cmod_Re_le h) as HR.
    assert (Rabs (Re h) < Re z) by lra.
    apply Rabs_def2 in H; lra. }
  assert (K1 : Cminus C1 (Cadd z h) <> C0).
  { intro Hc.
    assert (H' : Cminus C1 z = h)
      by (replace (Cminus C1 z) with (Cadd (Cminus C1 (Cadd z h)) h) by ring;
          rewrite Hc; ring).
    rewrite H' in Hhc; lra. }
  rewrite (zF_eq (Cadd z h) K0 K1), (zF_eq z H0 H1).
  exact (Hb h K0 K1 Hhdel).
Qed.

Corollary zF_holomorphic : HolomorphicOn zF inDom.
Proof. exact zF_holo. Qed.

Print Assumptions zF_holo.

(* ================================================================= *)
(*  END ZetaFn.v  —  zeta as a total holomorphic C -> C function.       *)
(* ================================================================= *)
