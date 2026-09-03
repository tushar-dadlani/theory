(* ================================================================= *)
(*  CArgPrincipleRect.v  --  the argument principle on a rectangle.   *)
(*                                                                    *)
(*    (1/2*pi*i) int_{d[x0,x1]x[y0,y1]} F'/F  =  length l              *)
(*                                                                    *)
(*  for F = prodfac l . G with G holomorphic and non-vanishing on a    *)
(*  convex open U carrying the contour, and every point of l strictly  *)
(*  inside the rectangle.  Repeats in l are allowed and are exactly    *)
(*  how multiplicity is carried, so the order-of-vanishing brick       *)
(*  f = (z-a)^m . g is never needed.                                   *)
(*                                                                    *)
(*  Assembly: CLogDerivList.logderiv_split splits the integrand        *)
(*  pointwise on the contour into sum_{w in l} 1/(z-w) plus the        *)
(*  cofactor term; RectWindingGen.rect_winding_interior gives 2*pi*i   *)
(*  per element of l; CLoopCofactor.rect_loop_region kills the         *)
(*  cofactor.  No complex logarithm anywhere.                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia List FunctionalExtensionality.
Require Import ComplexField Cmodulus Holomorphic CDeriv CDerivUnique
        CHoloCalculus CIntegral2 CSegInt CPathIntegral CGoursatLin
        CWinding CWindingOffCenter CTruncCauchy CPrimConv
        CPrimitive JensenMultiZero RectWinding RectWindingGen
        CLogDerivList CLoopCofactor.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Continuity of the pole-sum along a segment.                        *)
(* ----------------------------------------------------------------- *)

Lemma lsum_seg_wit : forall (l : list C) (P Q : C),
  (forall w u, In w l -> Cminus (seg P Q u) w <> C0) ->
  Ccont (fun u => Cmul (lsum l (seg P Q u)) (seg' P Q u)).
Proof.
  induction l as [ | w l' IH ]; intros P Q Hne.
  - apply (Ccont_congr (fun _ : R => C0));
      [ intro u; simpl; ring | apply Ccont_const ].
  - apply (Ccont_congr
             (fun u => Cadd (Cmul (Cinv (Cminus (seg P Q u) w)) (seg' P Q u))
                            (Cmul (lsum l' (seg P Q u)) (seg' P Q u)))).
    + intro u; simpl; ring.
    + apply Ccont_add.
      * apply Ccont_mul; [ apply Ccont_inv | apply Ccont_seg'_id ].
        -- apply (Ccont_congr (seg (Cminus P w) (Cminus Q w)));
             [ intro u; symmetry; apply seg_shift | apply Ccont_seg_id ].
        -- intro u; apply Hne; left; reflexivity.
      * apply IH; intros v u Hv; apply Hne; right; exact Hv.
Qed.

(* ----------------------------------------------------------------- *)
(*  Extensionality on the INTERVAL ONLY.  Cintf_ext demands the two    *)
(*  integrands agree everywhere, which is unusable here: F'/F is not   *)
(*  defined at the zeros and h agrees with G'/G only on U, whereas the *)
(*  segment map seg P Q u leaves U once u leaves [0,1].                *)
(* ----------------------------------------------------------------- *)

Lemma Cintf_ext_on : forall f g Hf Hg a b, a <= b ->
  (forall u, a < u < b -> f u = g u) ->
  Cintf f Hf a b = Cintf g Hg a b.
Proof.
  intros f g Hf Hg a b Hab Heq; unfold Cintf; apply Ceq; cbn [Re Im];
    apply RiemannInt_P18; solve
      [ exact Hab | intros x Hx; rewrite (Heq x Hx); reflexivity ].
Qed.

Lemma pathint_ext_on : forall gam gam' f g Hf Hg a b, a <= b ->
  (forall u, a < u < b -> f (gam u) = g (gam u)) ->
  pathint gam gam' f Hf a b = pathint gam gam' g Hg a b.
Proof.
  intros gam gam' f g Hf Hg a b Hab Heq; unfold pathint.
  apply Cintf_ext_on; [ exact Hab | ].
  intros u Hu; rewrite (Heq u Hu); reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  Splitting the pole-sum off a path integral.                        *)
(* ----------------------------------------------------------------- *)

Lemma pathint_lsum_nil : forall (gam gam' : R -> C) a b Hc,
  pathint gam gam' (lsum nil) Hc a b = C0.
Proof.
  intros gam gam' a b Hc; unfold pathint.
  transitivity (Cintf (fun _ : R => C0) (Ccont_const C0) a b).
  - apply Cintf_ext; intro u; simpl; ring.
  - rewrite Cintf_const_ab; apply Ceq; cbn; ring.
Qed.

Lemma pathint_lsum_cons : forall (gam gam' : R -> C) (w : C) (l : list C) a b
    (Hc : Ccont (fun u => Cmul (lsum (w :: l) (gam u)) (gam' u)))
    (Ha : Ccont (fun u => Cmul (Cinv (Cminus (gam u) w)) (gam' u)))
    (Hb : Ccont (fun u => Cmul (lsum l (gam u)) (gam' u))),
  a <= b ->
  pathint gam gam' (lsum (w :: l)) Hc a b
  = Cadd (pathint gam gam' (fun z => Cinv (Cminus z w)) Ha a b)
         (pathint gam gam' (lsum l) Hb a b).
Proof.
  intros gam gam' w l a b Hc Ha Hb Hab; unfold pathint.
  assert (Hsum : Ccont (fun u => Cadd (Cmul (Cinv (Cminus (gam u) w)) (gam' u))
                                      (Cmul (lsum l (gam u)) (gam' u))))
    by (apply Ccont_add; assumption).
  rewrite (Cintf_ext _ _ Hc Hsum a b); [ | intro u; simpl; ring ].
  apply Cintf_add; exact Hab.
Qed.

(* ----------------------------------------------------------------- *)
(*  One edge: the honest integrand F'/F becomes lsum + cofactor.       *)
(* ----------------------------------------------------------------- *)

Lemma edge_reduce : forall (U : C -> Prop) (F G Fd Gd h : C -> C) (l : list C)
    (Hcont : CcontC h) (P Q : C),
  Convex U -> U P -> U Q ->
  (forall u, F u = Cmul (prodfac l u) (G u)) ->
  (forall z, U z -> is_Cderiv F z (Fd z)) ->
  (forall z, U z -> is_Cderiv G z (Gd z)) ->
  (forall z, U z -> G z <> C0) ->
  (forall z, U z -> h z = Cmul (Gd z) (Cinv (G z))) ->
  (forall w u, In w l -> Cminus (seg P Q u) w <> C0) ->
  forall (M : Ccont (fun u => Cmul (Cmul (Fd (seg P Q u)) (Cinv (F (seg P Q u))))
                                   (seg' P Q u)))
         (Lw : Ccont (fun u => Cmul (lsum l (seg P Q u)) (seg' P Q u)))
         (Hw : Ccont (fun u => Cmul (h (seg P Q u)) (seg' P Q u))),
  pathint (seg P Q) (seg' P Q) (fun z => Cmul (Fd z) (Cinv (F z))) M 0 1
  = Cadd (pathint (seg P Q) (seg' P Q) (lsum l) Lw 0 1)
         (pathint (seg P Q) (seg' P Q) h Hw 0 1).
Proof.
  intros U F G Fd Gd h l Hcont P Q HU HUP HUQ Hfac HFd HGd HGne Hhag Hoff M Lw Hw.
  assert (Hsum : Ccont (fun u => Cmul (Cadd (lsum l (seg P Q u)) (h (seg P Q u)))
                                      (seg' P Q u))).
  { apply (Ccont_congr (fun u => Cadd (Cmul (lsum l (seg P Q u)) (seg' P Q u))
                                      (Cmul (h (seg P Q u)) (seg' P Q u))));
      [ intro u; ring | apply Ccont_add; assumption ]. }
  transitivity (pathint (seg P Q) (seg' P Q)
                  (fun z => Cadd (lsum l z) (h z)) Hsum 0 1).
  - apply pathint_ext_on; [ lra | ].
    intros u Hu.
    assert (HUz : U (seg P Q u)) by (apply HU; [ exact HUP | exact HUQ | lra ]).
    rewrite (Hhag _ HUz).
    apply (logderiv_split F G l (seg P Q u) (Fd (seg P Q u)) (Gd (seg P Q u)));
      [ exact Hfac
      | intros w Hw' Heq; apply (Hoff w u Hw'); rewrite Heq; ring
      | apply HGne; exact HUz
      | apply HFd; exact HUz
      | apply HGd; exact HUz ].
  - unfold pathint.
    assert (Hsp : Ccont (fun u => Cadd (Cmul (lsum l (seg P Q u)) (seg' P Q u))
                                       (Cmul (h (seg P Q u)) (seg' P Q u))))
      by (apply Ccont_add; assumption).
    rewrite (Cintf_ext _ _ Hsum Hsp 0 1); [ | intro u; ring ].
    apply Cintf_add; lra.
Qed.

(* ================================================================= *)
Section ArgPrinciple.

Variables (x0 x1 y0 y1 : R).
Hypothesis Hx : x0 < x1.
Hypothesis Hy : y0 < y1.

Let A : C := mkC x1 y0.
Let B : C := mkC x1 y1.
Let D : C := mkC x0 y1.
Let E : C := mkC x0 y0.

Definition Inside (w : C) : Prop := x0 < Re w < x1 /\ y0 < Im w < y1.

(* every edge stays off an interior point *)
Lemma edge_ne : forall w, Inside w -> forall u,
  Cminus (seg A B u) w <> C0 /\ Cminus (seg B D u) w <> C0 /\
  Cminus (seg D E u) w <> C0 /\ Cminus (seg E A u) w <> C0.
Proof.
  intros w [[Hw0 Hw1] [Hw2 Hw3]] u; unfold A, B, D, E.
  repeat split;
    solve [ apply vseg_ne0; lra | apply hseg_ne0; lra ].
Qed.

(* the four-edge sum of the pole-sum: one 2*pi*i per element of l *)
Lemma lsum_rect : forall (l : list C),
  (forall w, In w l -> Inside w) ->
  forall (H1 : Ccont (fun u => Cmul (lsum l (seg A B u)) (seg' A B u)))
         (H2 : Ccont (fun u => Cmul (lsum l (seg B D u)) (seg' B D u)))
         (H3 : Ccont (fun u => Cmul (lsum l (seg D E u)) (seg' D E u)))
         (H4 : Ccont (fun u => Cmul (lsum l (seg E A u)) (seg' E A u))),
  Cadd (pathint (seg A B) (seg' A B) (lsum l) H1 0 1)
  (Cadd (pathint (seg B D) (seg' B D) (lsum l) H2 0 1)
  (Cadd (pathint (seg D E) (seg' D E) (lsum l) H3 0 1)
        (pathint (seg E A) (seg' E A) (lsum l) H4 0 1)))
  = Cmul (RtoC (INR (length l))) (mkC 0 (2 * PI)).
Proof.
  induction l as [ | w l' IH ]; intros Hin H1 H2 H3 H4.
  - rewrite !pathint_lsum_nil; simpl; apply Ceq; cbn; ring.
  - assert (Hw : Inside w) by (apply Hin; left; reflexivity).
    assert (Htl : forall v, In v l' -> Inside v)
      by (intros v Hv; apply Hin; right; exact Hv).
    destruct Hw as [[Hw0 Hw1] [Hw2 Hw3]].
    (* witnesses for the single pole and for the tail, on each edge *)
    assert (Ka : Ccont (fun u => Cmul (Cinv (Cminus (seg A B u) w)) (seg' A B u)))
      by (unfold A, B; apply vseg_wit; lra).
    assert (Kb : Ccont (fun u => Cmul (Cinv (Cminus (seg B D u) w)) (seg' B D u)))
      by (unfold B, D; apply hseg_wit; lra).
    assert (Kc : Ccont (fun u => Cmul (Cinv (Cminus (seg D E u) w)) (seg' D E u)))
      by (unfold D, E; apply vseg_wit; lra).
    assert (Kd : Ccont (fun u => Cmul (Cinv (Cminus (seg E A u) w)) (seg' E A u)))
      by (unfold E, A; apply hseg_wit; lra).
    assert (La : Ccont (fun u => Cmul (lsum l' (seg A B u)) (seg' A B u)))
      by (apply lsum_seg_wit; intros v u Hv; apply (edge_ne v (Htl v Hv) u)).
    assert (Lb : Ccont (fun u => Cmul (lsum l' (seg B D u)) (seg' B D u)))
      by (apply lsum_seg_wit; intros v u Hv; apply (edge_ne v (Htl v Hv) u)).
    assert (Lc : Ccont (fun u => Cmul (lsum l' (seg D E u)) (seg' D E u)))
      by (apply lsum_seg_wit; intros v u Hv; apply (edge_ne v (Htl v Hv) u)).
    assert (Ld : Ccont (fun u => Cmul (lsum l' (seg E A u)) (seg' E A u)))
      by (apply lsum_seg_wit; intros v u Hv; apply (edge_ne v (Htl v Hv) u)).
    rewrite (pathint_lsum_cons _ _ w l' 0 1 H1 Ka La ltac:(lra)).
    rewrite (pathint_lsum_cons _ _ w l' 0 1 H2 Kb Lb ltac:(lra)).
    rewrite (pathint_lsum_cons _ _ w l' 0 1 H3 Kc Lc ltac:(lra)).
    rewrite (pathint_lsum_cons _ _ w l' 0 1 H4 Kd Ld ltac:(lra)).
    assert (Hwind :
      Cadd (pathint (seg A B) (seg' A B) (fun z => Cinv (Cminus z w)) Ka 0 1)
      (Cadd (pathint (seg B D) (seg' B D) (fun z => Cinv (Cminus z w)) Kb 0 1)
      (Cadd (pathint (seg D E) (seg' D E) (fun z => Cinv (Cminus z w)) Kc 0 1)
            (pathint (seg E A) (seg' E A) (fun z => Cinv (Cminus z w)) Kd 0 1)))
      = mkC 0 (2 * PI))
      by exact (rect_winding_interior w x0 x1 y0 y1 Hw0 Hw1 Hw2 Hw3 Ka Kb Kc Kd).
    assert (Htail := IH Htl La Lb Lc Ld).
    (* regroup: the four poles give 2*pi*i, the four tails give the IH *)
    transitivity (Cadd
      (Cadd (pathint (seg A B) (seg' A B) (fun z => Cinv (Cminus z w)) Ka 0 1)
      (Cadd (pathint (seg B D) (seg' B D) (fun z => Cinv (Cminus z w)) Kb 0 1)
      (Cadd (pathint (seg D E) (seg' D E) (fun z => Cinv (Cminus z w)) Kc 0 1)
            (pathint (seg E A) (seg' E A) (fun z => Cinv (Cminus z w)) Kd 0 1))))
      (Cadd (pathint (seg A B) (seg' A B) (lsum l') La 0 1)
      (Cadd (pathint (seg B D) (seg' B D) (lsum l') Lb 0 1)
      (Cadd (pathint (seg D E) (seg' D E) (lsum l') Lc 0 1)
            (pathint (seg E A) (seg' E A) (lsum l') Ld 0 1))))).
    + ring.
    + rewrite Hwind, Htail; simpl length; rewrite S_INR.
      apply Ceq; cbn; ring.
Qed.

(* ================================================================= *)
(*  THE ARGUMENT PRINCIPLE ON A RECTANGLE.                             *)
(* ================================================================= *)

Theorem arg_principle_rect :
  forall (U : C -> Prop) (F G Fd Gd h : C -> C) (l : list C) (Hcont : CcontC h),
  Convex U -> Open U ->
  U A -> U B -> U D -> U E ->
  (forall u, F u = Cmul (prodfac l u) (G u)) ->
  (forall z, U z -> is_Cderiv F z (Fd z)) ->
  (forall z, U z -> is_Cderiv G z (Gd z)) ->
  (forall z, U z -> G z <> C0) ->
  (forall z, U z -> exists d, is_Cderiv h z d) ->
  (forall z, U z -> h z = Cmul (Gd z) (Cinv (G z))) ->
  (forall w, In w l -> Inside w) ->
  forall
    (M1 : Ccont (fun u => Cmul (Cmul (Fd (seg A B u)) (Cinv (F (seg A B u))))
                               (seg' A B u)))
    (M2 : Ccont (fun u => Cmul (Cmul (Fd (seg B D u)) (Cinv (F (seg B D u))))
                               (seg' B D u)))
    (M3 : Ccont (fun u => Cmul (Cmul (Fd (seg D E u)) (Cinv (F (seg D E u))))
                               (seg' D E u)))
    (M4 : Ccont (fun u => Cmul (Cmul (Fd (seg E A u)) (Cinv (F (seg E A u))))
                               (seg' E A u))),
  Cadd (pathint (seg A B) (seg' A B) (fun z => Cmul (Fd z) (Cinv (F z))) M1 0 1)
  (Cadd (pathint (seg B D) (seg' B D) (fun z => Cmul (Fd z) (Cinv (F z))) M2 0 1)
  (Cadd (pathint (seg D E) (seg' D E) (fun z => Cmul (Fd z) (Cinv (F z))) M3 0 1)
        (pathint (seg E A) (seg' E A) (fun z => Cmul (Fd z) (Cinv (F z))) M4 0 1)))
  = Cmul (RtoC (INR (length l))) (mkC 0 (2 * PI)).
Proof.
  intros U F G Fd Gd h l Hcont HU HO HUA HUB HUD HUE Hfac HFd HGd HGne Hhol
         Hhag Hin M1 M2 M3 M4.
  (* no point of l lies on any edge *)
  assert (Oa : forall w u, In w l -> Cminus (seg A B u) w <> C0)
    by (intros w u Hw; exact (proj1 (edge_ne w (Hin w Hw) u))).
  assert (Ob : forall w u, In w l -> Cminus (seg B D u) w <> C0)
    by (intros w u Hw; exact (proj1 (proj2 (edge_ne w (Hin w Hw) u)))).
  assert (Oc : forall w u, In w l -> Cminus (seg D E u) w <> C0)
    by (intros w u Hw; exact (proj1 (proj2 (proj2 (edge_ne w (Hin w Hw) u))))).
  assert (Od : forall w u, In w l -> Cminus (seg E A u) w <> C0)
    by (intros w u Hw; exact (proj2 (proj2 (proj2 (edge_ne w (Hin w Hw) u))))).
  (* witnesses for the pole-sum and the cofactor on each edge *)
  assert (La : Ccont (fun u => Cmul (lsum l (seg A B u)) (seg' A B u)))
    by (apply lsum_seg_wit; exact Oa).
  assert (Lb : Ccont (fun u => Cmul (lsum l (seg B D u)) (seg' B D u)))
    by (apply lsum_seg_wit; exact Ob).
  assert (Lc : Ccont (fun u => Cmul (lsum l (seg D E u)) (seg' D E u)))
    by (apply lsum_seg_wit; exact Oc).
  assert (Ld : Ccont (fun u => Cmul (lsum l (seg E A u)) (seg' E A u)))
    by (apply lsum_seg_wit; exact Od).
  assert (Wa : Ccont (fun u => Cmul (h (seg A B u)) (seg' A B u)))
    by (apply Ccont_mul; [ apply Hcont, Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Wb : Ccont (fun u => Cmul (h (seg B D u)) (seg' B D u)))
    by (apply Ccont_mul; [ apply Hcont, Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Wc : Ccont (fun u => Cmul (h (seg D E u)) (seg' D E u)))
    by (apply Ccont_mul; [ apply Hcont, Ccont_seg_id | apply Ccont_seg'_id ]).
  assert (Wd : Ccont (fun u => Cmul (h (seg E A u)) (seg' E A u)))
    by (apply Ccont_mul; [ apply Hcont, Ccont_seg_id | apply Ccont_seg'_id ]).
  (* split each edge *)
  rewrite (edge_reduce U F G Fd Gd h l Hcont A B HU HUA HUB Hfac HFd HGd HGne
             Hhag Oa M1 La Wa).
  rewrite (edge_reduce U F G Fd Gd h l Hcont B D HU HUB HUD Hfac HFd HGd HGne
             Hhag Ob M2 Lb Wb).
  rewrite (edge_reduce U F G Fd Gd h l Hcont D E HU HUD HUE Hfac HFd HGd HGne
             Hhag Oc M3 Lc Wc).
  rewrite (edge_reduce U F G Fd Gd h l Hcont E A HU HUE HUA Hfac HFd HGd HGne
             Hhag Od M4 Ld Wd).
  assert (Hls := lsum_rect l Hin La Lb Lc Ld).
  assert (Hcof := rect_loop_region U HU HO h Hcont Hhol A B D E
                    HUA HUB HUD HUE Wa Wb Wc Wd).
  transitivity (Cadd
    (Cadd (pathint (seg A B) (seg' A B) (lsum l) La 0 1)
    (Cadd (pathint (seg B D) (seg' B D) (lsum l) Lb 0 1)
    (Cadd (pathint (seg D E) (seg' D E) (lsum l) Lc 0 1)
          (pathint (seg E A) (seg' E A) (lsum l) Ld 0 1))))
    (Cadd (pathint (seg A B) (seg' A B) h Wa 0 1)
    (Cadd (pathint (seg B D) (seg' B D) h Wb 0 1)
    (Cadd (pathint (seg D E) (seg' D E) h Wc 0 1)
          (pathint (seg E A) (seg' E A) h Wd 0 1))))).
  - ring.
  - rewrite Hls, Hcof; ring.
Qed.

End ArgPrinciple.

Print Assumptions lsum_rect.
Print Assumptions arg_principle_rect.

(* ================================================================= *)
(*  NON-VACUITY.  Instantiate at F z = z on [-1,1] x [-1,1]: one zero  *)
(*  at the origin, cofactor identically 1.  The theorem must compute   *)
(*  2*pi*i -- and at the empty list, 0.  A statement this heavily      *)
(*  hypothesised can be true for the wrong reason; this pins it.       *)
(* ================================================================= *)

Lemma Cvx : Convex (fun _ : C => True).
Proof. intros a b _ _ s _; exact I. Qed.

Lemma Opn : Open (fun _ : C => True).
Proof. intros z _; exists 1; split; [ lra | intros; exact I ]. Qed.

Lemma id_fac : forall u : C, u = Cmul (prodfac (C0 :: nil) u) ((fun _ => C1) u).
Proof. intro u; simpl; ring. Qed.

Theorem arg_principle_id :
  forall (M1 : Ccont (fun u => Cmul (Cmul C1 (Cinv (seg (mkC 1 (-1)) (mkC 1 1) u)))
                                    (seg' (mkC 1 (-1)) (mkC 1 1) u)))
         (M2 : Ccont (fun u => Cmul (Cmul C1 (Cinv (seg (mkC 1 1) (mkC (-1) 1) u)))
                                    (seg' (mkC 1 1) (mkC (-1) 1) u)))
         (M3 : Ccont (fun u => Cmul (Cmul C1 (Cinv (seg (mkC (-1) 1) (mkC (-1) (-1)) u)))
                                    (seg' (mkC (-1) 1) (mkC (-1) (-1)) u)))
         (M4 : Ccont (fun u => Cmul (Cmul C1 (Cinv (seg (mkC (-1) (-1)) (mkC 1 (-1)) u)))
                                    (seg' (mkC (-1) (-1)) (mkC 1 (-1)) u))),
  Cadd (pathint (seg (mkC 1 (-1)) (mkC 1 1)) (seg' (mkC 1 (-1)) (mkC 1 1))
                (fun z => Cmul C1 (Cinv z)) M1 0 1)
  (Cadd (pathint (seg (mkC 1 1) (mkC (-1) 1)) (seg' (mkC 1 1) (mkC (-1) 1))
                 (fun z => Cmul C1 (Cinv z)) M2 0 1)
  (Cadd (pathint (seg (mkC (-1) 1) (mkC (-1) (-1))) (seg' (mkC (-1) 1) (mkC (-1) (-1)))
                 (fun z => Cmul C1 (Cinv z)) M3 0 1)
        (pathint (seg (mkC (-1) (-1)) (mkC 1 (-1))) (seg' (mkC (-1) (-1)) (mkC 1 (-1)))
                 (fun z => Cmul C1 (Cinv z)) M4 0 1)))
  = mkC 0 (2 * PI).
Proof.
  intros M1 M2 M3 M4.
  assert (HR0 : Re C0 = 0) by reflexivity.
  assert (HI0 : Im C0 = 0) by reflexivity.
  transitivity (Cmul (RtoC (INR (length (C0 :: nil)))) (mkC 0 (2 * PI))).
  - apply (arg_principle_rect (-1) 1 (-1) 1
             (fun _ : C => True) (fun z => z) (fun _ => C1) (fun _ => C1)
             (fun _ => C0) (fun _ => C0) (C0 :: nil) (CcontC_const C0)
             Cvx Opn I I I I id_fac);
      try (intros; exact I).
    + intros z _; apply Cderiv_id.
    + intros z _; apply Cderiv_const.
    + intros z _; intro Hc; apply (f_equal Re) in Hc; cbn in Hc; lra.
    + intros z _; exists C0; apply Cderiv_const.
    + intros z _; field; intro Hc; apply (f_equal Re) in Hc; cbn in Hc; lra.
    + intros w Hw; simpl in Hw; destruct Hw as [ Heq | [] ]; subst w.
        unfold Inside. rewrite HR0, HI0. repeat split; lra.
  - simpl length; rewrite INR_1; apply Ceq; cbn; ring.
Qed.

Print Assumptions arg_principle_id.

(* ================================================================= *)
(*  END CArgPrincipleRect.v (part 1) -- the pole-sum contributes       *)
(*  2*pi*i per element of l.                                           *)
(* ================================================================= *)
