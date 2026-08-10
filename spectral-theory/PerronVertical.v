(* ================================================================= *)
(*  PerronVertical.v  —  Perron A1d: the vertical-line integral Vperron   *)
(*  and the right-edge change of variables.                             *)
(*                                                                    *)
(*  Vraw y c T := ∫_{−T}^{T} y^{c+it}/(c+it) dt   (the raw vertical        *)
(*  Perron integral); Vperron := Vraw/(2π).  The right edge of the         *)
(*  Perron rectangle, seg (c−iT)(c+iT), is (via the substitution           *)
(*  t = −T+2Tu and Cintf_cov) exactly  i·Vraw:                            *)
(*                                                                    *)
(*    right_edge_Vraw :  ∮_right y^s/s ds  =  i · Vraw.                    *)
(*                                                                    *)
(*  This is the bridge from the rectangle residue to the truncated        *)
(*  Perron statement.  Axiom-clean.                                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CLeibniz CSegCoV
        CPathIntegral CexpFull PerronPower RectWinding PerronKernel.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  continuity helpers                                                *)
(* ----------------------------------------------------------------- *)

Lemma Ccont_comp_R : forall (f : R -> C) (g : R -> R),
  Ccont f -> (forall x, continuity_pt g x) -> Ccont (fun u => f (g u)).
Proof.
  intros f g [HfR HfI] Hg; split; intro x.
  - apply (continuity_pt_comp g (fun u => Re (f u)) x); [ apply Hg | apply HfR ].
  - apply (continuity_pt_comp g (fun u => Im (f u)) x); [ apply Hg | apply HfI ].
Qed.

Lemma Ld_cont : forall p q x, continuity_pt (Ld p q) x.
Proof. intros p q x; apply derivable_continuous_pt; exists (q - p); apply Ld_deriv. Qed.

Lemma mkC_c_cont : forall c, Ccont (fun t => mkC c t).
Proof.
  intro c; split; intro x;
    [ apply continuity_pt_const; intros a b; reflexivity
    | apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id ].
Qed.

Lemma mkC_c_ne0 : forall c t, c <> 0 -> mkC c t <> C0.
Proof. intros c t Hc H; apply Hc; apply (f_equal Re) in H; cbn in H; exact H. Qed.

Lemma Cmul_mkC0_i : forall (G : C) (r : R), Cmul G (mkC 0 r) = Cmul Ci (Cmul (RtoC r) G).
Proof. intros G r; unfold Cmul, Ci, RtoC; apply Ceq; cbn; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  the vertical Perron integrand and its integral                    *)
(* ----------------------------------------------------------------- *)

Definition Gint (y c t : R) : C := Cmul (Cpw y (mkC c t)) (Cinv (mkC c t)).

Lemma Gint_cont : forall y c, c <> 0 -> Ccont (Gint y c).
Proof.
  intros y c Hc; unfold Gint; apply Ccont_mul.
  - apply (CcontC_Cpw y (fun t => mkC c t) (mkC_c_cont c)).
  - apply Ccont_Cinv_comp; [ apply mkC_c_cont | intro u; apply mkC_c_ne0; exact Hc ].
Qed.

Definition Vraw (y c T : R) (Hc : c <> 0) : C := Cintf (Gint y c) (Gint_cont y c Hc) (- T) T.
Definition Vperron (y c T : R) (Hc : c <> 0) : C := Cmul (RtoC (/ (2 * PI))) (Vraw y c T Hc).

(* ----------------------------------------------------------------- *)
(*  the right edge = i·Vraw                                            *)
(* ----------------------------------------------------------------- *)

Theorem right_edge_Vraw : forall y c T (Hc : c <> 0) (HT : 0 < T)
  (HfF : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c (- T)) (mkC c T) u))
                          (Cinv (seg (mkC c (- T)) (mkC c T) u))) (seg' (mkC c (- T)) (mkC c T) u))),
  pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T))
          (fun z => Cmul (Cpw y z) (Cinv z)) HfF 0 1
  = Cmul Ci (Vraw y c T Hc).
Proof.
  intros y c T Hc HT HfF; unfold pathint.
  assert (Hf3 : Ccont (fun u => Cmul (RtoC (T - - T)) (Gint y c (Ld (- T) T u)))).
  { apply Ccont_scal; apply (Ccont_comp_R (Gint y c) (Ld (- T) T) (Gint_cont y c Hc));
      intro x; apply Ld_cont. }
  assert (Hf2 : Ccont (fun u => Cmul Ci (Cmul (RtoC (T - - T)) (Gint y c (Ld (- T) T u)))))
    by (apply Ccont_scal; exact Hf3).
  assert (Hmap : forall t, 0 <= t <= 1 -> Ld (- T) T 0 <= Ld (- T) T t <= Ld (- T) T 1)
    by (intros t Ht; rewrite Ld_0, Ld_1; unfold Ld; nra).
  assert (Hg'c : forall t, 0 <= t <= 1 -> continuity_pt (fun _ : R => T - - T) t)
    by (intros; apply continuity_pt_const; intros a b; reflexivity).
  rewrite (Cintf_ext
    (fun u => Cmul (Cmul (Cpw y (seg (mkC c (- T)) (mkC c T) u))
                (Cinv (seg (mkC c (- T)) (mkC c T) u))) (seg' (mkC c (- T)) (mkC c T) u))
    (fun u => Cmul Ci (Cmul (RtoC (T - - T)) (Gint y c (Ld (- T) T u))))
    HfF Hf2 0 1).
  2:{ intro u; rewrite segv, segv'.
      change (Cmul (Cpw y (mkC c (Ld (- T) T u))) (Cinv (mkC c (Ld (- T) T u))))
        with (Gint y c (Ld (- T) T u)).
      apply Cmul_mkC0_i. }
  rewrite (Cintf_cmul_l Ci (fun u => Cmul (RtoC (T - - T)) (Gint y c (Ld (- T) T u)))
             Hf3 Hf2 0 1 Rle_0_1).
  f_equal.
  rewrite (Cintf_cov (Gint y c) (Ld (- T) T) (fun _ => T - - T) 0 1
             (Gint_cont y c Hc) Hf3 Rle_0_1
             (fun t _ => Ld_deriv (- T) T t) Hg'c Hmap).
  unfold Vraw; rewrite Ld_0, Ld_1; reflexivity.
Qed.

Print Assumptions right_edge_Vraw.

(* ================================================================= *)
(*  END PerronVertical.v (CoV step) — right edge = i·Vraw.  Next: the    *)
(*  horizontal-edge decay + left-edge → 0 + U→∞, giving perron_gt1.      *)
(* ================================================================= *)
