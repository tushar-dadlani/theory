(* ================================================================= *)
(*  ExplicitFormulaPole01.v  —  Explicit formula, Stage A brick 2:       *)
(*  the residue of the 1/(s-1)-part of the Perron kernel (s=1 AND s=0).   *)
(*                                                                    *)
(*  Phi(s) = 1/(s-1) + PhiMinus(s)  (ZetaPoleCancel), so the elementary   *)
(*  part of the explicit-formula kernel  Phi(s) x^s/s  is  x^s/(s(s-1)).  *)
(*  Its poles inside the contour are s=1 (residue x, the main term) and   *)
(*  s=0 (residue -1).  We compute the whole contour integral:             *)
(*                                                                    *)
(*    rect_residue_pole01 :  K01 y s = y^s/(s(s-1))  integrated ccw around *)
(*    the rectangle [-Uu,c] x [-T,T]  (contains both 0 and 1 since        *)
(*    -Uu < 0 and c > 1)  equals  2*pi*i*(y-1).                           *)
(*                                                                    *)
(*  Mechanism: the partial fraction 1/(s(s-1)) = 1/(s-1) - 1/s (pf01)     *)
(*  splits each edge integral (Cintf_ext_ab + Cintf_sub, valid since the  *)
(*  edges avoid 0 and 1), reducing to  rect_residue_pole1 (s=1 -> 2*pi*i*y)*)
(*  minus  PerronKernel.perron_rect_residue (s=0 -> 2*pi*i).              *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CIntegral2 CPathIntegral CSegInt
        CLeibniz PerronKernel PerronPower ThetaTailEntire CTruncCauchy
        PiecewiseTransform ExplicitFormulaMainTerm.
Open Scope R_scope.

Definition K01 (y : R) (s : C) : C := Cmul (Cpw y s) (Cinv (Cmul s (Cminus s C1))).

(* continuity of  u |-> Cpw y (seg P Q u) *)
Lemma cont_pw_seg : forall y P Q, Ccont (fun u => Cpw y (seg P Q u)).
Proof.
  intros y P Q. unfold Cpw.
  apply Ccont_Cexpf. apply Ccont_mul; [ apply Ccont_seg_id | apply Ccont_const ].
Qed.

(* the generic Perron-kernel integrand is continuous when the denominator is *)
Lemma cont_kernel : forall y P Q (den : R -> C),
  Ccont den -> (forall u, den u <> C0) ->
  Ccont (fun u => Cmul (Cmul (Cpw y (seg P Q u)) (Cinv (den u))) (seg' P Q u)).
Proof.
  intros y P Q den Hden Hne. apply Ccont_mul; [ apply Ccont_mul | apply Ccont_seg'_id ].
  - apply cont_pw_seg.
  - apply Ccont_Cinv_comp; assumption.
Qed.

(* the partial fraction  1/(s(s-1)) = 1/(s-1) - 1/s *)
Lemma pf01 : forall s, s <> C0 -> Cminus s C1 <> C0 ->
  Cinv (Cmul s (Cminus s C1)) = Cminus (Cinv (Cminus s C1)) (Cinv s).
Proof. intros s H0 H1. field. split; assumption. Qed.

(* segments avoid  1  (vertical edge off Re=1;  horizontal edge off Im=0) *)
Lemma seg_ne1_v : forall a p q u, a <> 1 -> seg (mkC a p) (mkC a q) u <> C1.
Proof.
  intros a p q u Ha Hc. apply (f_equal Re) in Hc.
  unfold seg, Cadd, Cmul, Cminus, RtoC, C1 in Hc; cbn [Re Im] in Hc. apply Ha. lra.
Qed.
Lemma seg_ne1_h : forall p q b u, b <> 0 -> seg (mkC p b) (mkC q b) u <> C1.
Proof.
  intros p q b u Hb Hc. apply (f_equal Im) in Hc.
  unfold seg, Cadd, Cmul, Cminus, RtoC, C1 in Hc; cbn [Re Im] in Hc. apply Hb. lra.
Qed.

(* one edge:  int K01 = int K1 - int KER0 *)
Lemma edge01 : forall y P Q
  (Hh : Ccont (fun u => Cmul (K01 y (seg P Q u)) (seg' P Q u)))
  (Hf : Ccont (fun u => Cmul (K1 y (seg P Q u)) (seg' P Q u)))
  (Hr : Ccont (fun u => Cmul (Cmul (Cpw y (seg P Q u)) (Cinv (seg P Q u))) (seg' P Q u))),
  (forall u, 0 < u < 1 -> seg P Q u <> C0) ->
  (forall u, 0 < u < 1 -> seg P Q u <> C1) ->
  pathint (seg P Q) (seg' P Q) (K01 y) Hh 0 1
  = Cminus (pathint (seg P Q) (seg' P Q) (K1 y) Hf 0 1)
           (pathint (seg P Q) (seg' P Q) (fun z => Cmul (Cpw y z) (Cinv z)) Hr 0 1).
Proof.
  intros y P Q Hh Hf Hr H0 H1. unfold pathint.
  transitivity (Cintf (fun u => Cminus (Cmul (K1 y (seg P Q u)) (seg' P Q u))
                                       (Cmul (Cmul (Cpw y (seg P Q u)) (Cinv (seg P Q u)))
                                             (seg' P Q u)))
                 (Ccont_sub _ _ Hf Hr) 0 1).
  - apply Cintf_ext_ab; [ lra | ]. intros u Hu. unfold K01, K1.
    rewrite (pf01 (seg P Q u) (H0 u Hu)).
    2:{ intro Hc. apply (H1 u Hu). apply Ceq;
        [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
        unfold Cminus, C0, C1 in *; cbn [Re Im] in *; lra. }
    set (a := Cpw y (seg P Q u)). set (b := seg' P Q u).
    set (iS := Cinv (seg P Q u)). set (iS1 := Cinv (Cminus (seg P Q u) C1)). ring.
  - apply Cintf_sub. lra.
Qed.

Lemma seg_m1_ne0_v : forall a p q u, a <> 1 -> Cminus (seg (mkC a p) (mkC a q) u) C1 <> C0.
Proof.
  intros a p q u Ha Hc. apply (seg_ne1_v a p q u Ha).
  apply Ceq; [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
    unfold Cminus, C0, C1 in *; cbn [Re Im] in *; lra.
Qed.
Lemma seg_m1_ne0_h : forall p q b u, b <> 0 -> Cminus (seg (mkC p b) (mkC q b) u) C1 <> C0.
Proof.
  intros p q b u Hb Hc. apply (seg_ne1_h p q b u Hb).
  apply Ceq; [ apply (f_equal Re) in Hc | apply (f_equal Im) in Hc ];
    unfold Cminus, C0, C1 in *; cbn [Re Im] in *; lra.
Qed.

(* the residue of the 1/(s-1)-part kernel  y^s/(s(s-1))  around the rectangle
   [-Uu,c] x [-T,T]  (contains s=0 and s=1 since -Uu<0 and c>1):  2 pi i (y-1). *)
Theorem rect_residue_pole01 : forall (y c Uu T : R),
  0 < y -> 1 < c -> 0 < Uu -> 0 < T ->
  forall
    (Hh1 : Ccont (fun u => Cmul (K01 y (seg (mkC c (- T)) (mkC c T) u))
                                (seg' (mkC c (- T)) (mkC c T) u)))
    (Hh2 : Ccont (fun u => Cmul (K01 y (seg (mkC c T) (mkC (- Uu) T) u))
                                (seg' (mkC c T) (mkC (- Uu) T) u)))
    (Hh3 : Ccont (fun u => Cmul (K01 y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u))
                                (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
    (Hh4 : Ccont (fun u => Cmul (K01 y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u))
                                (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T)) (K01 y) Hh1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC (- Uu) T)) (seg' (mkC c T) (mkC (- Uu) T)) (K01 y) Hh2 0 1)
  (Cadd (pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T))) (K01 y) Hh3 0 1)
        (pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) (seg' (mkC (- Uu) (- T)) (mkC c (- T))) (K01 y) Hh4 0 1)))
  = mkC 0 (2 * PI * (y - 1)).
Proof.
  intros y c Uu T Hy Hc HU HT Hh1 Hh2 Hh3 Hh4.
  (* --- K1 over R edges --- *)
  assert (Hf1 : Ccont (fun u => Cmul (K1 y (seg (mkC c (- T)) (mkC c T) u)) (seg' (mkC c (- T)) (mkC c T) u)))
    by (unfold K1; apply (cont_kernel y (mkC c (- T)) (mkC c T) (fun u => Cminus (seg (mkC c (- T)) (mkC c T) u) C1));
        [ apply Ccont_sub; [ apply Ccont_seg_id | apply Ccont_const ]
        | intro u; apply seg_m1_ne0_v; lra ]).
  assert (Hf2 : Ccont (fun u => Cmul (K1 y (seg (mkC c T) (mkC (- Uu) T) u)) (seg' (mkC c T) (mkC (- Uu) T) u)))
    by (unfold K1; apply (cont_kernel y (mkC c T) (mkC (- Uu) T) (fun u => Cminus (seg (mkC c T) (mkC (- Uu) T) u) C1));
        [ apply Ccont_sub; [ apply Ccont_seg_id | apply Ccont_const ]
        | intro u; apply seg_m1_ne0_h; lra ]).
  assert (Hf3 : Ccont (fun u => Cmul (K1 y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u)) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
    by (unfold K1; apply (cont_kernel y (mkC (- Uu) T) (mkC (- Uu) (- T)) (fun u => Cminus (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u) C1));
        [ apply Ccont_sub; [ apply Ccont_seg_id | apply Ccont_const ]
        | intro u; apply seg_m1_ne0_v; lra ]).
  assert (Hf4 : Ccont (fun u => Cmul (K1 y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u)) (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u)))
    by (unfold K1; apply (cont_kernel y (mkC (- Uu) (- T)) (mkC c (- T)) (fun u => Cminus (seg (mkC (- Uu) (- T)) (mkC c (- T)) u) C1));
        [ apply Ccont_sub; [ apply Ccont_seg_id | apply Ccont_const ]
        | intro u; apply seg_m1_ne0_h; lra ]).
  (* --- KER0 over R edges --- *)
  assert (Hr1 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c (- T)) (mkC c T) u)) (Cinv (seg (mkC c (- T)) (mkC c T) u))) (seg' (mkC c (- T)) (mkC c T) u)))
    by (apply (cont_kernel y (mkC c (- T)) (mkC c T) (seg (mkC c (- T)) (mkC c T)));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_v; lra ]).
  assert (Hr2 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c T) (mkC (- Uu) T) u)) (Cinv (seg (mkC c T) (mkC (- Uu) T) u))) (seg' (mkC c T) (mkC (- Uu) T) u)))
    by (apply (cont_kernel y (mkC c T) (mkC (- Uu) T) (seg (mkC c T) (mkC (- Uu) T)));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_h; lra ]).
  assert (Hr3 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u)) (Cinv (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
    by (apply (cont_kernel y (mkC (- Uu) T) (mkC (- Uu) (- T)) (seg (mkC (- Uu) T) (mkC (- Uu) (- T))));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_v; lra ]).
  assert (Hr4 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u)) (Cinv (seg (mkC (- Uu) (- T)) (mkC c (- T)) u))) (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u)))
    by (apply (cont_kernel y (mkC (- Uu) (- T)) (mkC c (- T)) (seg (mkC (- Uu) (- T)) (mkC c (- T))));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_h; lra ]).
  (* --- KER0 over R' (= R shifted left by 1) edges, for rect_residue_pole1 --- *)
  assert (Hg1 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (c - 1) (- T)) (mkC (c - 1) T) u)) (Cinv (seg (mkC (c - 1) (- T)) (mkC (c - 1) T) u))) (seg' (mkC (c - 1) (- T)) (mkC (c - 1) T) u)))
    by (apply (cont_kernel y (mkC (c - 1) (- T)) (mkC (c - 1) T) (seg (mkC (c - 1) (- T)) (mkC (c - 1) T)));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_v; lra ]).
  assert (Hg2 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (c - 1) T) (mkC (- (Uu + 1)) T) u)) (Cinv (seg (mkC (c - 1) T) (mkC (- (Uu + 1)) T) u))) (seg' (mkC (c - 1) T) (mkC (- (Uu + 1)) T) u)))
    by (apply (cont_kernel y (mkC (c - 1) T) (mkC (- (Uu + 1)) T) (seg (mkC (c - 1) T) (mkC (- (Uu + 1)) T)));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_h; lra ]).
  assert (Hg3 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)) u)) (Cinv (seg (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)) u))) (seg' (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)) u)))
    by (apply (cont_kernel y (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)) (seg (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T))));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_v; lra ]).
  assert (Hg4 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)) u)) (Cinv (seg (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)) u))) (seg' (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)) u)))
    by (apply (cont_kernel y (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)) (seg (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T))));
        [ apply Ccont_seg_id | intro u; apply seg_ne0_h; lra ]).
  (* --- decompose each K01 edge into K1 - KER0 --- *)
  rewrite (edge01 y (mkC c (- T)) (mkC c T) Hh1 Hf1 Hr1
             ltac:(intros u _; apply seg_ne0_v; lra) ltac:(intros u _; apply seg_ne1_v; lra)).
  rewrite (edge01 y (mkC c T) (mkC (- Uu) T) Hh2 Hf2 Hr2
             ltac:(intros u _; apply seg_ne0_h; lra) ltac:(intros u _; apply seg_ne1_h; lra)).
  rewrite (edge01 y (mkC (- Uu) T) (mkC (- Uu) (- T)) Hh3 Hf3 Hr3
             ltac:(intros u _; apply seg_ne0_v; lra) ltac:(intros u _; apply seg_ne1_v; lra)).
  rewrite (edge01 y (mkC (- Uu) (- T)) (mkC c (- T)) Hh4 Hf4 Hr4
             ltac:(intros u _; apply seg_ne0_h; lra) ltac:(intros u _; apply seg_ne1_h; lra)).
  (* --- sum of K1 edges = 2 pi i y ;  sum of KER0 edges = 2 pi i --- *)
  pose proof (rect_residue_pole1 y c Uu T Hy Hc HU HT Hf1 Hf2 Hf3 Hf4 Hg1 Hg2 Hg3 Hg4) as HK1.
  pose proof (perron_rect_residue y c Uu T Hy ltac:(lra) HU HT Hr1 Hr2 Hr3 Hr4) as HK0.
  set (A1 := pathint (seg (mkC c (- T)) (mkC c T)) _ (K1 y) Hf1 0 1) in *.
  set (A2 := pathint (seg (mkC c T) (mkC (- Uu) T)) _ (K1 y) Hf2 0 1) in *.
  set (A3 := pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) _ (K1 y) Hf3 0 1) in *.
  set (A4 := pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) _ (K1 y) Hf4 0 1) in *.
  set (B1 := pathint (seg (mkC c (- T)) (mkC c T)) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hr1 0 1) in *.
  set (B2 := pathint (seg (mkC c T) (mkC (- Uu) T)) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hr2 0 1) in *.
  set (B3 := pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hr3 0 1) in *.
  set (B4 := pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hr4 0 1) in *.
  replace (Cadd (Cminus A1 B1) (Cadd (Cminus A2 B2) (Cadd (Cminus A3 B3) (Cminus A4 B4))))
    with (Cminus (Cadd A1 (Cadd A2 (Cadd A3 A4))) (Cadd B1 (Cadd B2 (Cadd B3 B4)))) by ring.
  rewrite HK1, HK0. apply Ceq; unfold Cminus; cbn [Re Im]; ring.
Qed.

Print Assumptions rect_residue_pole01.
