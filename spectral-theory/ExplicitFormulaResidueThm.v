(* ================================================================= *)
(*  ExplicitFormulaResidueThm.v  —  Explicit formula, Stage B brick 2:   *)
(*  the residue theorem for a single simple pole (Stage-B capstone).      *)
(*                                                                    *)
(*  Combining Stage B brick 1 (CauchyRectangle.rect_cauchy) with the      *)
(*  Stage-A residue  ExplicitFormulaPoleZero.rect_residue_poleC  gives the *)
(*  textbook residue theorem:  for an ENTIRE h, the contour integral of   *)
(*                                                                    *)
(*      h(s) + y^s/(s - a)                                               *)
(*                                                                    *)
(*  ccw around the a-centred rectangle  a + [-Uu,c] x [-T,T]  equals the   *)
(*      2*pi*i * y^a   ( = Cmul (mkC 0 (2*pi)) (Cpw y a) ),               *)
(*  i.e. 2*pi*i times the residue at s = a.  The entire part contributes  *)
(*  NOTHING (rect_cauchy), and the simple pole contributes exactly its    *)
(*  residue (rect_residue_poleC).                                         *)
(*                                                                    *)
(*  This is the residue-theorem content of Stage B, assembled and         *)
(*  axiom-clean.  Reading it against the explicit formula: the kernel      *)
(*  Phi(s) x^s/s, near a pole a (= 1, 0, or a zero rho), splits as         *)
(*  (residue)*x^s/(s-a) + (locally holomorphic), and this theorem says the *)
(*  contour picks off exactly the residue.  What remains (Stage C) is the  *)
(*  GLOBAL analytic input -- a region-restricted Cauchy for the actual     *)
(*  meromorphic Phi (infinitely many zero-poles) and the growth bounds     *)
(*  that make the far contour edges vanish -- which the entire-function    *)
(*  rect_cauchy here does not supply.                                     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CIntegral2 CPathIntegral CSegInt
        CTriangle CGoursat CGoursatLin CLeibniz PerronKernel PerronPower Holomorphic
        CauchyRectangle CTruncCauchy ExplicitFormulaPole01 ExplicitFormulaPoleZero.
Open Scope R_scope.

(* seg over an a-shifted pair is the a-shift of the seg *)
Lemma seg_add_sub : forall (a P0 Q0 : C) u,
  Cminus (seg (Cadd a P0) (Cadd a Q0) u) a = seg P0 Q0 u.
Proof.
  intros a P0 Q0 u. unfold seg. apply Ceq;
    unfold Cadd, Cmul, Cminus, RtoC; cbn [Re Im]; ring.
Qed.

(* seg_int = pathint (same integrand; continuity-proof irrelevance) *)
Lemma seg_int_is_pathint : forall (f : C -> C) (Hf : CcontC f) (P Q : C) Hp,
  seg_int f Hf P Q = pathint (seg P Q) (seg' P Q) f Hp 0 1.
Proof. intros. unfold seg_int, pathint. apply Cintf_irrel. Qed.

(* one edge:  int (h + y^s/(s-a)) = int h + int y^s/(s-a) *)
Lemma pathint_split_hK : forall (h : C -> C) y a P Q Hs Hh Hk,
  pathint (seg P Q) (seg' P Q) (fun s => Cadd (h s) (KpoleC y a s)) Hs 0 1
  = Cadd (pathint (seg P Q) (seg' P Q) h Hh 0 1)
         (pathint (seg P Q) (seg' P Q) (KpoleC y a) Hk 0 1).
Proof.
  intros h y a P Q Hs Hh Hk. unfold pathint.
  transitivity (Cintf (fun u => Cadd (Cmul (h (seg P Q u)) (seg' P Q u))
                                     (Cmul (KpoleC y a (seg P Q u)) (seg' P Q u)))
                 (Ccont_add _ _ Hh Hk) 0 1).
  - apply Cintf_ext. intro u. unfold KpoleC. ring.
  - exact (Cintf_add _ _ Hh Hk (Ccont_add _ _ Hh Hk) 0 1 Rle_0_1).
Qed.

(* THE RESIDUE THEOREM (single simple pole).  For an ENTIRE h, the contour
   integral of  h(s) + y^s/(s-a)  ccw around the a-centred rectangle equals the
   residue  2*pi*i * y^a  -- the entire part contributes nothing (rect_cauchy),
   and the pole contributes its residue (rect_residue_poleC). *)
Theorem residue_theorem_1pole :
  forall (h : C -> C) (Hcont : CcontC h) (Hhol : forall z, exists d, is_Cderiv h z d)
         (y : R) (a : C) (c Uu T : R),
  0 < y -> 0 < c -> 0 < Uu -> 0 < T ->
  forall
    (Hs1 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T)) u)) (seg' (Cadd a (mkC c (- T))) (Cadd a (mkC c T)) u)))
    (Hs2 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T)) u)) (seg' (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T)) u)))
    (Hs3 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T))) u)) (seg' (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T))) u)))
    (Hs4 : Ccont (fun u => Cmul ((fun s => Cadd (h s) (KpoleC y a s)) (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T))) u)) (seg' (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T))) u))),
  Cadd (pathint (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) (seg' (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) (fun s => Cadd (h s) (KpoleC y a s)) Hs1 0 1)
  (Cadd (pathint (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) (seg' (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) (fun s => Cadd (h s) (KpoleC y a s)) Hs2 0 1)
  (Cadd (pathint (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) (seg' (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) (fun s => Cadd (h s) (KpoleC y a s)) Hs3 0 1)
        (pathint (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) (seg' (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) (fun s => Cadd (h s) (KpoleC y a s)) Hs4 0 1)))
  = Cmul (mkC 0 (2 * PI)) (Cpw y a).
Proof.
  intros h Hcont Hhol y a c Uu T Hy Hc HU HT Hs1 Hs2 Hs3 Hs4.
  (* denominators nonzero: on the a-centred edges,  s - a = (perron seg) <> 0 *)
  assert (Dne : forall (P0 Q0 : C) u, (forall v, seg P0 Q0 v <> C0) ->
             Cminus (seg (Cadd a P0) (Cadd a Q0) u) a <> C0)
    by (intros P0 Q0 u Hpq; rewrite seg_add_sub; apply Hpq).
  (* KpoleC integrand continuity on each a-centred edge (cont_kernel) *)
  assert (HkC : forall (P0 Q0 : C), (forall v, seg P0 Q0 v <> C0) ->
    Ccont (fun u => Cmul (KpoleC y a (seg (Cadd a P0) (Cadd a Q0) u)) (seg' (Cadd a P0) (Cadd a Q0) u))).
  { intros P0 Q0 Hpq. unfold KpoleC.
    apply (cont_kernel y (Cadd a P0) (Cadd a Q0)
             (fun u => Cminus (seg (Cadd a P0) (Cadd a Q0) u) a)).
    - apply Ccont_sub; [ apply Ccont_seg_id | apply Ccont_const ].
    - intro u. apply Dne; exact Hpq. }
  (* KER0 integrand continuity on each perron edge *)
  assert (Hr0 : forall (P0 Q0 : C), (forall v, seg P0 Q0 v <> C0) ->
    Ccont (fun u => Cmul (Cmul (Cpw y (seg P0 Q0 u)) (Cinv (seg P0 Q0 u))) (seg' P0 Q0 u)))
    by (intros P0 Q0 Hpq; apply (cont_kernel y P0 Q0 (seg P0 Q0)); [ apply Ccont_seg_id | exact Hpq ]).
  set (Hk1 := HkC (mkC c (- T)) (mkC c T) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hk2 := HkC (mkC c T) (mkC (- Uu) T) ltac:(intro v; apply seg_ne0_h; lra)).
  set (Hk3 := HkC (mkC (- Uu) T) (mkC (- Uu) (- T)) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hk4 := HkC (mkC (- Uu) (- T)) (mkC c (- T)) ltac:(intro v; apply seg_ne0_h; lra)).
  set (Hg1 := Hr0 (mkC c (- T)) (mkC c T) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hg2 := Hr0 (mkC c T) (mkC (- Uu) T) ltac:(intro v; apply seg_ne0_h; lra)).
  set (Hg3 := Hr0 (mkC (- Uu) T) (mkC (- Uu) (- T)) ltac:(intro v; apply seg_ne0_v; lra)).
  set (Hg4 := Hr0 (mkC (- Uu) (- T)) (mkC c (- T)) ltac:(intro v; apply seg_ne0_h; lra)).
  (* split each edge into h-part + pole-part *)
  rewrite (pathint_split_hK h y a _ _ Hs1 (seg_ig_cont h Hcont _ _) Hk1).
  rewrite (pathint_split_hK h y a _ _ Hs2 (seg_ig_cont h Hcont _ _) Hk2).
  rewrite (pathint_split_hK h y a _ _ Hs3 (seg_ig_cont h Hcont _ _) Hk3).
  rewrite (pathint_split_hK h y a _ _ Hs4 (seg_ig_cont h Hcont _ _) Hk4).
  (* h-parts sum to 0 (rect_cauchy);  pole-parts sum to 2 pi i y^a (poleC) *)
  pose proof (rect_cauchy h Hcont Hhol (Cadd a (mkC c (- T))) (Cadd a (mkC c T))
                (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) as HC.
  rewrite !(seg_int_is_pathint h Hcont _ _ (seg_ig_cont h Hcont _ _)) in HC.
  pose proof (rect_residue_poleC y a c Uu T Hy Hc HU HT Hk1 Hk2 Hk3 Hk4 Hg1 Hg2 Hg3 Hg4) as HP.
  set (h1 := pathint (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) _ h _ 0 1) in *.
  set (h2 := pathint (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) _ h _ 0 1) in *.
  set (h3 := pathint (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) _ h _ 0 1) in *.
  set (h4 := pathint (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) _ h _ 0 1) in *.
  set (k1 := pathint (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) _ (KpoleC y a) Hk1 0 1) in *.
  set (k2 := pathint (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) _ (KpoleC y a) Hk2 0 1) in *.
  set (k3 := pathint (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) _ (KpoleC y a) Hk3 0 1) in *.
  set (k4 := pathint (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) _ (KpoleC y a) Hk4 0 1) in *.
  (* HC : h1+h2+h3+h4 = 0 ;  HP : k1+k2+k3+k4 = 2 pi i y^a *)
  replace (Cadd (Cadd h1 k1) (Cadd (Cadd h2 k2) (Cadd (Cadd h3 k3) (Cadd h4 k4))))
    with (Cadd (Cadd h1 (Cadd h2 (Cadd h3 h4))) (Cadd k1 (Cadd k2 (Cadd k3 k4)))) by ring.
  rewrite HC, HP. ring.
Qed.

Print Assumptions residue_theorem_1pole.
