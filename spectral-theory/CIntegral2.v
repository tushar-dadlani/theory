(* ================================================================= *)
(*  CIntegral2.v  —  Milestone C, brick C1a: a GENERAL finite C-valued  *)
(*  integral for an arbitrary continuous f : R -> C.                    *)
(*                                                                    *)
(*  Generalizes CFTC.CgderivInt (hard-wired to gderivC) to any f whose  *)
(*  Re/Im components are continuous, via cont_RI.  Provides the algebra  *)
(*  (Re/Im projection, Chasles additivity, linearity) and the ML        *)
(*  inequality Cmod (Cintf f a b) <= 2 M (b-a) for |f| <= M on [a,b] --  *)
(*  the substrate for contour integrals (C1b) and Newman's estimates.   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CSeries CImproperIntegral.
Open Scope R_scope.

(* ---- continuous C-valued functions of a real variable ---- *)
Definition Ccont (f : R -> C) : Prop :=
  continuity (fun u => Re (f u)) /\ continuity (fun u => Im (f u)).

Lemma Ccont_const : forall c : C, Ccont (fun _ => c).
Proof. intro c; split; intro x; apply continuity_pt_const; intro; reflexivity. Qed.

Lemma Ccont_add : forall f g, Ccont f -> Ccont g -> Ccont (fun u => Cadd (f u) (g u)).
Proof.
  intros f g [Hfr Hfi] [Hgr Hgi]; split; intro x;
    [ apply (continuity_pt_plus (fun u => Re (f u)) (fun u => Re (g u)))
    | apply (continuity_pt_plus (fun u => Im (f u)) (fun u => Im (g u))) ];
    solve [ apply Hfr | apply Hfi | apply Hgr | apply Hgi ].
Qed.

Lemma Ccont_opp : forall f, Ccont f -> Ccont (fun u => Copp (f u)).
Proof.
  intros f [Hfr Hfi]; split; intro x.
  - assert (Heq : (fun u => Re (Copp (f u))) = (fun u => 0 - Re (f u)))
      by (apply functional_extensionality; intro u; unfold Copp; cbn [Re]; ring).
    rewrite Heq; apply continuity_pt_minus;
      [ apply continuity_pt_const; intro; reflexivity | apply Hfr ].
  - assert (Heq : (fun u => Im (Copp (f u))) = (fun u => 0 - Im (f u)))
      by (apply functional_extensionality; intro u; unfold Copp; cbn [Im]; ring).
    rewrite Heq; apply continuity_pt_minus;
      [ apply continuity_pt_const; intro; reflexivity | apply Hfi ].
Qed.

Lemma Ccont_mul : forall f g, Ccont f -> Ccont g -> Ccont (fun u => Cmul (f u) (g u)).
Proof.
  intros f g [Hfr Hfi] [Hgr Hgi]; split; intro x.
  - assert (Heq : (fun u => Re (Cmul (f u) (g u)))
      = (fun u => Re (f u) * Re (g u) - Im (f u) * Im (g u)))
      by (apply functional_extensionality; intro u; unfold Cmul; cbn [Re]; ring).
    rewrite Heq; apply continuity_pt_minus; apply continuity_pt_mult; auto.
  - assert (Heq : (fun u => Im (Cmul (f u) (g u)))
      = (fun u => Re (f u) * Im (g u) + Im (f u) * Re (g u)))
      by (apply functional_extensionality; intro u; unfold Cmul; cbn [Im]; ring).
    rewrite Heq; apply continuity_pt_plus; apply continuity_pt_mult; auto.
Qed.

Lemma Ccont_scal : forall c f, Ccont f -> Ccont (fun u => Cmul c (f u)).
Proof. intros c f Hf; apply Ccont_mul; [ apply Ccont_const | exact Hf ]. Qed.

(* ---- the general finite C-valued integral ---- *)
Definition Cintf (f : R -> C) (Hf : Ccont f) (a b : R) : C :=
  mkC (RiemannInt (cont_RI _ (proj1 Hf) a b))
      (RiemannInt (cont_RI _ (proj2 Hf) a b)).

Lemma Re_Cintf : forall f Hf a b,
  Re (Cintf f Hf a b) = RiemannInt (cont_RI _ (proj1 Hf) a b).
Proof. reflexivity. Qed.

Lemma Im_Cintf : forall f Hf a b,
  Im (Cintf f Hf a b) = RiemannInt (cont_RI _ (proj2 Hf) a b).
Proof. reflexivity. Qed.

(* ---- Chasles additivity (any a,b,c) ---- *)
Lemma Cintf_additive : forall f Hf a b c,
  Cintf f Hf a c = Cadd (Cintf f Hf a b) (Cintf f Hf b c).
Proof.
  intros f Hf a b c; apply Ceq; unfold Cadd; cbn [Re Im].
  - symmetry; apply RiemannInt_P26.
  - symmetry; apply RiemannInt_P26.
Qed.

(* ---- proof-irrelevance in the continuity witness ---- *)
Lemma Cintf_irrel : forall f Hf Hf' a b, Cintf f Hf a b = Cintf f Hf' a b.
Proof.
  intros f Hf Hf' a b; apply Ceq; cbn [Re Im]; apply RiemannInt_P5.
Qed.

(* ---- reversal ---- *)
Lemma Cintf_swap : forall f Hf a b, Cintf f Hf b a = Copp (Cintf f Hf a b).
Proof.
  intros f Hf a b; apply Ceq; unfold Copp; cbn [Re Im];
    apply RiemannInt_P8.
Qed.

(* ---- a real helper: |∫ g| <= M (b-a) when |g| <= M on [a,b] ---- *)
Lemma RInt_abs_bound : forall (g : R -> R) a b (pr : Riemann_integrable g a b) M,
  a <= b -> (forall x, a <= x <= b -> Rabs (g x) <= M) ->
  Rabs (RiemannInt pr) <= M * (b - a).
Proof.
  intros g a b pr M Hab Hbd.
  eapply Rle_trans; [ apply (RiemannInt_P17 pr (RiemannInt_P16 pr) Hab) | ].
  apply Rle_trans with (RiemannInt (RiemannInt_P14 a b M)).
  - apply RiemannInt_P19; [ exact Hab | ].
    intros x Hx; unfold fct_cte; apply Hbd; lra.
  - rewrite RiemannInt_P15; apply Rle_refl.
Qed.

(* ---- THE finite ML inequality ---- *)
Lemma Cintf_ML : forall f Hf a b M, a <= b ->
  (forall u, a <= u <= b -> Cmod (f u) <= M) ->
  Cmod (Cintf f Hf a b) <= 2 * M * (b - a).
Proof.
  intros f Hf a b M Hab Hbd.
  eapply Rle_trans; [ apply Cmod_le_sum | ].
  rewrite Re_Cintf, Im_Cintf.
  assert (HRe : Rabs (RiemannInt (cont_RI _ (proj1 Hf) a b)) <= M * (b - a)).
  { apply RInt_abs_bound; [ exact Hab | ].
    intros x Hx; eapply Rle_trans; [ apply Cmod_Re | apply Hbd; exact Hx ]. }
  assert (HIm : Rabs (RiemannInt (cont_RI _ (proj2 Hf) a b)) <= M * (b - a)).
  { apply RInt_abs_bound; [ exact Hab | ].
    intros x Hx; eapply Rle_trans; [ apply Cmod_Im | apply Hbd; exact Hx ]. }
  lra.
Qed.

Print Assumptions Cintf_additive.
Print Assumptions Cintf_ML.

(* ================================================================= *)
(*  END CIntegral2.v  —  the general finite C-valued integral.          *)
(* ================================================================= *)
