(* ================================================================= *)
(*  RectWindingGen.v  --  the winding of an axis-aligned rectangle     *)
(*  around an ARBITRARY interior point:                                *)
(*                                                                    *)
(*      int_{d[x0,x1]x[y0,y1]} dz/(z-w) = 2*pi*i,   w strictly inside.  *)
(*                                                                    *)
(*  RectWinding.rect_winding does the pole at 0 with a rectangle       *)
(*  [-U,c] x [-T,T], i.e. vertically SYMMETRIC about the pole; and     *)
(*  ExplicitFormulaPoleZero.rect_residue_poleC does an arbitrary pole  *)
(*  but again only for a rectangle symmetric about it.  Neither can be *)
(*  aimed at a fixed box holding several zeros at different heights,   *)
(*  which is what a counting contour needs.                            *)
(*                                                                    *)
(*  No new analysis: RectWinding.vseg_winding / hseg_winding are       *)
(*  already fully general in the segment endpoints, and translating a  *)
(*  segment by -w is a ring identity (vseg_shift / hseg_shift below).  *)
(*  So the whole content is atan bookkeeping.  Writing the four        *)
(*  shifted half-widths as POSITIVE quantities                         *)
(*      a1 = x1-Re w, a0 = Re w-x0, b1 = y1-Im w, b0 = Im w-y0,        *)
(*  the eight atan terms pair into four reciprocal pairs               *)
(*      (b1/a1, a1/b1), (b0/a1, a1/b0), (a0/b1, b1/a0), (b0/a0, a0/b0) *)
(*  each summing to pi/2 by atan_compl -- total 2*pi.  The symmetric   *)
(*  case needs only two such pairs, which is why the existing proof is *)
(*  shorter.  The Re parts telescope by ring, exactly as there.        *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral
        CWinding CWindingOffCenter CTruncWind CTruncCauchy RectWinding.
Open Scope R_scope.

Lemma ln_sq_comm : forall u v : R, ln (u * u + v * v) = ln (v * v + u * u).
Proof. intros u v; f_equal; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  Translating a segment: the shifted integrand is the same map.      *)
(* ----------------------------------------------------------------- *)

Lemma seg_shift : forall (w P Q : C) u,
  Cminus (seg P Q u) w = seg (Cminus P w) (Cminus Q w) u.
Proof. intros; unfold seg, Cadd, Cmul, Cminus, RtoC; apply Ceq; cbn; ring. Qed.

Lemma seg'_shift : forall (w P Q : C) u,
  seg' P Q u = seg' (Cminus P w) (Cminus Q w) u.
Proof. intros; unfold seg', Cminus; apply Ceq; cbn; ring. Qed.

Lemma mkC_shift : forall (w : C) (a b : R),
  Cminus (mkC a b) w = mkC (a - Re w) (b - Im w).
Proof. intros; unfold Cminus; apply Ceq; cbn; ring. Qed.

(* ---- the two shifted segment integrals ---- *)

Lemma vseg_winding_at : forall (w : C) (a p q : R), a - Re w <> 0 ->
  forall (Hf : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC a p) (mkC a q) u) w))
                                    (seg' (mkC a p) (mkC a q) u))),
  pathint (seg (mkC a p) (mkC a q)) (seg' (mkC a p) (mkC a q))
          (fun z => Cinv (Cminus z w)) Hf 0 1
  = mkC (/ 2 * ln ((q - Im w) * (q - Im w) + (a - Re w) * (a - Re w))
         - / 2 * ln ((p - Im w) * (p - Im w) + (a - Re w) * (a - Re w)))
        (atan ((q - Im w) / (a - Re w)) - atan ((p - Im w) / (a - Re w))).
Proof.
  intros w a p q Ha Hf.
  set (P := mkC (a - Re w) (p - Im w)).
  set (Q := mkC (a - Re w) (q - Im w)).
  assert (Hne : forall u, seg P Q u <> C0).
  { intros u Hc; apply (f_equal Re) in Hc; unfold P, Q in Hc; cbn in Hc.
    apply Ha; lra. }
  assert (Hg : Ccont (fun u => Cmul (Cinv (seg P Q u)) (seg' P Q u)))
    by (apply Ccont_mul;
        [ apply Ccont_inv; [ apply Ccont_seg_id | exact Hne ]
        | apply Ccont_seg'_id ]).
  transitivity (pathint (seg P Q) (seg' P Q) Cinv Hg 0 1).
  - unfold pathint; apply Cintf_ext; intro u.
    unfold P, Q; rewrite <- !mkC_shift, <- seg_shift, <- (seg'_shift w).
    reflexivity.
  - exact (vseg_winding (a - Re w) (p - Im w) (q - Im w) Ha Hg).
Qed.

Lemma hseg_winding_at : forall (w : C) (p q b : R), b - Im w <> 0 ->
  forall (Hf : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC p b) (mkC q b) u) w))
                                    (seg' (mkC p b) (mkC q b) u))),
  pathint (seg (mkC p b) (mkC q b)) (seg' (mkC p b) (mkC q b))
          (fun z => Cinv (Cminus z w)) Hf 0 1
  = mkC (/ 2 * ln ((q - Re w) * (q - Re w) + (b - Im w) * (b - Im w))
         - / 2 * ln ((p - Re w) * (p - Re w) + (b - Im w) * (b - Im w)))
        (- (atan ((q - Re w) / (b - Im w)) - atan ((p - Re w) / (b - Im w)))).
Proof.
  intros w p q b Hb Hf.
  set (P := mkC (p - Re w) (b - Im w)).
  set (Q := mkC (q - Re w) (b - Im w)).
  assert (Hne : forall u, seg P Q u <> C0).
  { intros u Hc; apply (f_equal Im) in Hc; unfold P, Q in Hc; cbn in Hc.
    apply Hb; lra. }
  assert (Hg : Ccont (fun u => Cmul (Cinv (seg P Q u)) (seg' P Q u)))
    by (apply Ccont_mul;
        [ apply Ccont_inv; [ apply Ccont_seg_id | exact Hne ]
        | apply Ccont_seg'_id ]).
  transitivity (pathint (seg P Q) (seg' P Q) Cinv Hg 0 1).
  - unfold pathint; apply Cintf_ext; intro u.
    unfold P, Q; rewrite <- !mkC_shift, <- seg_shift, <- (seg'_shift w).
    reflexivity.
  - exact (hseg_winding (p - Re w) (q - Re w) (b - Im w) Hb Hg).
Qed.

(* ================================================================= *)
(*  THE GENERAL RECTANGLE WINDING NUMBER.                              *)
(*  Corners, counterclockwise:                                         *)
(*    (x1,y0) -> (x1,y1) -> (x0,y1) -> (x0,y0) -> (x1,y0).             *)
(* ================================================================= *)

Theorem rect_winding_interior : forall (w : C) (x0 x1 y0 y1 : R),
  x0 < Re w -> Re w < x1 -> y0 < Im w -> Im w < y1 ->
  forall (Hf1 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC x1 y0) (mkC x1 y1) u) w))
                                     (seg' (mkC x1 y0) (mkC x1 y1) u)))
         (Hf2 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC x1 y1) (mkC x0 y1) u) w))
                                     (seg' (mkC x1 y1) (mkC x0 y1) u)))
         (Hf3 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC x0 y1) (mkC x0 y0) u) w))
                                     (seg' (mkC x0 y1) (mkC x0 y0) u)))
         (Hf4 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC x0 y0) (mkC x1 y0) u) w))
                                     (seg' (mkC x0 y0) (mkC x1 y0) u))),
  Cadd (pathint (seg (mkC x1 y0) (mkC x1 y1)) (seg' (mkC x1 y0) (mkC x1 y1))
                (fun z => Cinv (Cminus z w)) Hf1 0 1)
  (Cadd (pathint (seg (mkC x1 y1) (mkC x0 y1)) (seg' (mkC x1 y1) (mkC x0 y1))
                 (fun z => Cinv (Cminus z w)) Hf2 0 1)
  (Cadd (pathint (seg (mkC x0 y1) (mkC x0 y0)) (seg' (mkC x0 y1) (mkC x0 y0))
                 (fun z => Cinv (Cminus z w)) Hf3 0 1)
        (pathint (seg (mkC x0 y0) (mkC x1 y0)) (seg' (mkC x0 y0) (mkC x1 y0))
                 (fun z => Cinv (Cminus z w)) Hf4 0 1)))
  = mkC 0 (2 * PI).
Proof.
  intros w x0 x1 y0 y1 Hx0 Hx1 Hy0 Hy1 Hf1 Hf2 Hf3 Hf4.
  (* the four half-widths, as positive quantities *)
  assert (Ha1 : 0 < x1 - Re w) by lra.
  assert (Ha0 : 0 < Re w - x0) by lra.
  assert (Hb1 : 0 < y1 - Im w) by lra.
  assert (Hb0 : 0 < Im w - y0) by lra.
  rewrite (vseg_winding_at w x1 y0 y1 ltac:(lra) Hf1).
  rewrite (hseg_winding_at w x1 x0 y1 ltac:(lra) Hf2).
  rewrite (vseg_winding_at w x0 y1 y0 ltac:(lra) Hf3).
  rewrite (hseg_winding_at w x0 x1 y0 ltac:(lra) Hf4).
  unfold Cadd; apply Ceq; cbn [Re Im].
  - (* the ln terms telescope -- but the cancelling pairs are COMMUTED
       (b1*b1+a1*a1 vs a1*a1+b1*b1) and ring treats ln as opaque, so the
       arguments must be normalised first *)
    rewrite (ln_sq_comm (y1 - Im w) (x1 - Re w)),
            (ln_sq_comm (y0 - Im w) (x1 - Re w)),
            (ln_sq_comm (x0 - Re w) (y1 - Im w)),
            (ln_sq_comm (y0 - Im w) (x0 - Re w)).
    ring.
  - (* the eight atan terms pair into four reciprocal pairs *)
    replace ((y0 - Im w) / (x1 - Re w))
      with (- ((Im w - y0) / (x1 - Re w))) by (field; lra).
    replace ((x0 - Re w) / (y1 - Im w))
      with (- ((Re w - x0) / (y1 - Im w))) by (field; lra).
    replace ((y0 - Im w) / (x0 - Re w))
      with ((Im w - y0) / (Re w - x0)) by (field; lra).
    replace ((y1 - Im w) / (x0 - Re w))
      with (- ((y1 - Im w) / (Re w - x0))) by (field; lra).
    replace ((x1 - Re w) / (y0 - Im w))
      with (- ((x1 - Re w) / (Im w - y0))) by (field; lra).
    replace ((x0 - Re w) / (y0 - Im w))
      with ((Re w - x0) / (Im w - y0)) by (field; lra).
    rewrite !atan_opp.
    pose proof (atan_compl ((y1 - Im w) / (x1 - Re w))
                  (Rdiv_lt_0_compat _ _ Hb1 Ha1)) as H1.
    pose proof (atan_compl ((Im w - y0) / (x1 - Re w))
                  (Rdiv_lt_0_compat _ _ Hb0 Ha1)) as H2.
    pose proof (atan_compl ((Re w - x0) / (y1 - Im w))
                  (Rdiv_lt_0_compat _ _ Ha0 Hb1)) as H3.
    pose proof (atan_compl ((Im w - y0) / (Re w - x0))
                  (Rdiv_lt_0_compat _ _ Hb0 Ha0)) as H4.
    replace (/ ((y1 - Im w) / (x1 - Re w)))
      with ((x1 - Re w) / (y1 - Im w)) in H1 by (field; lra).
    replace (/ ((Im w - y0) / (x1 - Re w)))
      with ((x1 - Re w) / (Im w - y0)) in H2 by (field; lra).
    replace (/ ((Re w - x0) / (y1 - Im w)))
      with ((y1 - Im w) / (Re w - x0)) in H3 by (field; lra).
    replace (/ ((Im w - y0) / (Re w - x0)))
      with ((Re w - x0) / (Im w - y0)) in H4 by (field; lra).
    lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Non-vanishing of the shifted edges, and the Ccont witnesses every   *)
(*  caller has to supply.                                              *)
(* ----------------------------------------------------------------- *)

Lemma Ccont_congr : forall f g, (forall u, f u = g u) -> Ccont f -> Ccont g.
Proof.
  intros f g Heq Hf.
  assert (Hfe : f = g) by (apply functional_extensionality; exact Heq).
  rewrite <- Hfe; exact Hf.
Qed.

Lemma vseg_ne0 : forall (w : C) (a p q : R) u, a - Re w <> 0 ->
  Cminus (seg (mkC a p) (mkC a q) u) w <> C0.
Proof.
  intros w a p q u Ha Hc; apply (f_equal Re) in Hc.
  rewrite seg_shift, !mkC_shift in Hc; cbn in Hc; apply Ha; lra.
Qed.

Lemma hseg_ne0 : forall (w : C) (p q b : R) u, b - Im w <> 0 ->
  Cminus (seg (mkC p b) (mkC q b) u) w <> C0.
Proof.
  intros w p q b u Hb Hc; apply (f_equal Im) in Hc.
  rewrite seg_shift, !mkC_shift in Hc; cbn in Hc; apply Hb; lra.
Qed.

Lemma vseg_wit : forall (w : C) (a p q : R), a - Re w <> 0 ->
  Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC a p) (mkC a q) u) w))
                       (seg' (mkC a p) (mkC a q) u)).
Proof.
  intros w a p q Ha; apply Ccont_mul; [ apply Ccont_inv | apply Ccont_seg'_id ].
  - apply (Ccont_congr (seg (Cminus (mkC a p) w) (Cminus (mkC a q) w)));
      [ intro u; symmetry; apply seg_shift | apply Ccont_seg_id ].
  - intro u; apply vseg_ne0; exact Ha.
Qed.

Lemma hseg_wit : forall (w : C) (p q b : R), b - Im w <> 0 ->
  Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC p b) (mkC q b) u) w))
                       (seg' (mkC p b) (mkC q b) u)).
Proof.
  intros w p q b Hb; apply Ccont_mul; [ apply Ccont_inv | apply Ccont_seg'_id ].
  - apply (Ccont_congr (seg (Cminus (mkC p b) w) (Cminus (mkC q b) w)));
      [ intro u; symmetry; apply seg_shift | apply Ccont_seg_id ].
  - intro u; apply hseg_ne0; exact Hb.
Qed.

(* ----------------------------------------------------------------- *)
(*  Non-vacuity: the origin-centred RectWinding.rect_winding is the     *)
(*  w = C0 instance, which pins the orientation and the endpoint order. *)
(* ----------------------------------------------------------------- *)

Theorem rect_winding_origin : forall (c U T : R), 0 < c -> 0 < U -> 0 < T ->
  forall (Hf1 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC c (- T)) (mkC c T) u) C0))
                                     (seg' (mkC c (- T)) (mkC c T) u)))
         (Hf2 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC c T) (mkC (- U) T) u) C0))
                                     (seg' (mkC c T) (mkC (- U) T) u)))
         (Hf3 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC (- U) T) (mkC (- U) (- T)) u) C0))
                                     (seg' (mkC (- U) T) (mkC (- U) (- T)) u)))
         (Hf4 : Ccont (fun u => Cmul (Cinv (Cminus (seg (mkC (- U) (- T)) (mkC c (- T)) u) C0))
                                     (seg' (mkC (- U) (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T))
                (fun z => Cinv (Cminus z C0)) Hf1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC (- U) T)) (seg' (mkC c T) (mkC (- U) T))
                 (fun z => Cinv (Cminus z C0)) Hf2 0 1)
  (Cadd (pathint (seg (mkC (- U) T) (mkC (- U) (- T))) (seg' (mkC (- U) T) (mkC (- U) (- T)))
                 (fun z => Cinv (Cminus z C0)) Hf3 0 1)
        (pathint (seg (mkC (- U) (- T)) (mkC c (- T))) (seg' (mkC (- U) (- T)) (mkC c (- T)))
                 (fun z => Cinv (Cminus z C0)) Hf4 0 1)))
  = mkC 0 (2 * PI).
Proof.
  intros c U T Hc HU HT Hf1 Hf2 Hf3 Hf4.
  assert (HR0 : Re C0 = 0) by reflexivity.
  assert (HI0 : Im C0 = 0) by reflexivity.
  apply (rect_winding_interior C0 (- U) c (- T) T); rewrite ?HR0, ?HI0; lra.
Qed.

Print Assumptions rect_winding_interior.
Print Assumptions rect_winding_origin.

(* ================================================================= *)
(*  END RectWindingGen.v -- one 2*pi*i for each zero inside any        *)
(*  axis-aligned counting box.                                         *)
(* ================================================================= *)
