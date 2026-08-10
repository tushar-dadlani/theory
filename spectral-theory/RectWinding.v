(* ================================================================= *)
(*  RectWinding.v  —  Perron milestone A1b: the winding of an axis-      *)
(*  aligned rectangle around 0 equals 2πi.                              *)
(*                                                                    *)
(*  The rectangle (corners c−iT, c+iT, −U+iT, −U−iT; 0<c,U,T so it        *)
(*  encloses 0) has two vertical and two horizontal edges.  Over each    *)
(*  edge ∫ dz/z splits (as in CTruncWind) into a Re part ½·ln|·|² and a   *)
(*  Im part atan(·) via the FTC.  The Re parts telescope to 0 around the  *)
(*  closed loop; the Im parts sum to 2π via atan(x)+atan(1/x)=π/2         *)
(*  (atan_inv), applied to T/c and U/T.  Axiom-clean.                    *)
(*                                                                    *)
(*  General segment lemmas vseg_winding / hseg_winding (any vertical /   *)
(*  horizontal segment integral of 1/z) are also reusable for the        *)
(*  vertical-line Perron kernel downstream.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia.
Require Import ComplexField Cmodulus CImproperIntegral CIntegral2
        CPathIntegral CSegInt CWinding ContinuousCoV CTruncWind.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Shared denominator machinery:  Ld = affine coordinate along seg,   *)
(*  Den = Ld² + k²  (k = the fixed coordinate).                        *)
(* ----------------------------------------------------------------- *)

Definition Ld (p q s : R) : R := p + s * (q - p).
Definition Den (k p q s : R) : R := Ld p q s * Ld p q s + k * k.

Lemma Ld_0 : forall p q, Ld p q 0 = p.
Proof. intros; unfold Ld; ring. Qed.
Lemma Ld_1 : forall p q, Ld p q 1 = q.
Proof. intros; unfold Ld; ring. Qed.

Lemma Den_pos : forall k p q s, k <> 0 -> 0 < Den k p q s.
Proof.
  intros k p q s Hk; unfold Den.
  assert (Hkk : 0 < k * k) by (destruct (Rdichotomy k 0 Hk); nra).
  pose proof (Rle_0_sqr (Ld p q s)) as H; unfold Rsqr in H; nra.
Qed.

Lemma Ld_deriv : forall p q s, derivable_pt_lim (Ld p q) s (q - p).
Proof.
  intros p q s eps Heps; exists (mkposreal 1 Rlt_0_1); intros h Hh0 _.
  unfold Ld.
  replace ((p + (s + h) * (q - p) - (p + s * (q - p))) / h - (q - p)) with 0
    by (field; exact Hh0).
  rewrite Rabs_R0; exact Heps.
Qed.

Lemma Den_deriv : forall k p q s,
  derivable_pt_lim (Den k p q) s (2 * Ld p q s * (q - p)).
Proof.
  intros k p q s; unfold Den.
  replace (2 * Ld p q s * (q - p))
    with ((q - p) * Ld p q s + Ld p q s * (q - p) + 0) by ring.
  apply derivable_pt_lim_plus.
  - apply (derivable_pt_lim_mult (Ld p q) (Ld p q) s (q - p) (q - p)); apply Ld_deriv.
  - apply derivable_pt_lim_const.
Qed.

(* Re antiderivative:  ½·ln Den *)
Definition GReg (k p q s : R) : R := / 2 * ln (Den k p q s).

Lemma GReg_deriv : forall k p q s, k <> 0 ->
  derivable_pt_lim (GReg k p q) s (Ld p q s * (q - p) / Den k p q s).
Proof.
  intros k p q s Hk.
  assert (Hcomp : derivable_pt_lim (fun s => ln (Den k p q s)) s
                    (/ Den k p q s * (2 * Ld p q s * (q - p)))).
  { apply (derivable_pt_lim_comp (Den k p q) ln s
             (2 * Ld p q s * (q - p)) (/ Den k p q s)).
    - apply Den_deriv.
    - apply derivable_pt_lim_ln, Den_pos; exact Hk. }
  unfold GReg.
  replace (Ld p q s * (q - p) / Den k p q s)
    with (/ 2 * (/ Den k p q s * (2 * Ld p q s * (q - p))))
    by (field; apply Rgt_not_eq, Den_pos; exact Hk).
  exact (derivable_pt_lim_scal (fun s => ln (Den k p q s)) (/ 2) s
           (/ Den k p q s * (2 * Ld p q s * (q - p))) Hcomp).
Qed.

(* the inner atan argument Ld/k and its algebra *)
Definition Ginng (k p q s : R) : R := Ld p q s / k.

Lemma Ginng_deriv : forall k p q s, k <> 0 ->
  derivable_pt_lim (Ginng k p q) s ((q - p) / k).
Proof.
  intros k p q s Hk eps Heps; exists (mkposreal 1 Rlt_0_1); intros h Hh0 _.
  unfold Ginng, Ld.
  replace (((p + (s + h) * (q - p)) / k - (p + s * (q - p)) / k) / h - (q - p) / k)
    with 0 by (field; split; [ exact Hk | exact Hh0 ]).
  rewrite Rabs_R0; exact Heps.
Qed.

Lemma one_plus_innerg : forall k p q s, k <> 0 ->
  1 + (Ginng k p q s) ^ 2 = Den k p q s / (k * k).
Proof. intros k p q s Hk; unfold Ginng, Den, Ld; field; exact Hk. Qed.

(* ----------------------------------------------------------------- *)
(*  VERTICAL segment  mkC a p → mkC a q  (constant Re = a):             *)
(*    Im antiderivative +atan(Ld/a).                                   *)
(* ----------------------------------------------------------------- *)

Definition GImv (a p q s : R) : R := atan (Ginng a p q s).

Lemma GImv_deriv : forall a p q s, a <> 0 ->
  derivable_pt_lim (GImv a p q) s (a * (q - p) / Den a p q s).
Proof.
  intros a p q s Ha.
  assert (Hcomp : derivable_pt_lim (fun s => atan (Ginng a p q s)) s
                    (/ (1 + (Ginng a p q s) ^ 2) * ((q - p) / a))).
  { apply (derivable_pt_lim_comp (Ginng a p q) atan s
             ((q - p) / a) (/ (1 + (Ginng a p q s) ^ 2))).
    - apply Ginng_deriv; exact Ha.
    - apply derivable_pt_lim_atan. }
  unfold GImv.
  assert (HN : Den a p q s <> 0) by (apply Rgt_not_eq, Den_pos; exact Ha).
  assert (Haa : a * a <> 0) by (apply Rmult_integral_contrapositive_currified; exact Ha).
  replace (a * (q - p) / Den a p q s)
    with (/ (1 + (Ginng a p q s) ^ 2) * ((q - p) / a)).
  2:{ rewrite (one_plus_innerg a p q s Ha); field; repeat split; assumption. }
  exact Hcomp.
Qed.

Lemma segv : forall a p q s, seg (mkC a p) (mkC a q) s = mkC a (Ld p q s).
Proof. intros; unfold seg, Ld, Cadd, Cmul, Cminus, RtoC; apply Ceq; cbn; ring. Qed.
Lemma segv' : forall a p q s, seg' (mkC a p) (mkC a q) s = mkC 0 (q - p).
Proof. intros; unfold seg', Cminus; apply Ceq; cbn; ring. Qed.
Lemma Cnorm2v : forall a p q s, Cnorm2 (mkC a (Ld p q s)) = Den a p q s.
Proof. intros; unfold Cnorm2, Den; cbn [Re Im]; ring. Qed.

Lemma vchord_Re : forall a p q s, a <> 0 ->
  Re (Cmul (Cinv (seg (mkC a p) (mkC a q) s)) (seg' (mkC a p) (mkC a q) s))
  = Ld p q s * (q - p) / Den a p q s.
Proof.
  intros a p q s Ha; rewrite segv, segv'.
  unfold Cmul, Cinv; cbn [Re Im]; rewrite !Cnorm2v.
  field; apply Rgt_not_eq, Den_pos; exact Ha.
Qed.
Lemma vchord_Im : forall a p q s, a <> 0 ->
  Im (Cmul (Cinv (seg (mkC a p) (mkC a q) s)) (seg' (mkC a p) (mkC a q) s))
  = a * (q - p) / Den a p q s.
Proof.
  intros a p q s Ha; rewrite segv, segv'.
  unfold Cmul, Cinv; cbn [Re Im]; rewrite !Cnorm2v.
  field; apply Rgt_not_eq, Den_pos; exact Ha.
Qed.

Lemma vseg_winding : forall (a p q : R) (Ha : a <> 0)
  (Hf : Ccont (fun u => Cmul (Cinv (seg (mkC a p) (mkC a q) u))
                             (seg' (mkC a p) (mkC a q) u))),
  pathint (seg (mkC a p) (mkC a q)) (seg' (mkC a p) (mkC a q)) Cinv Hf 0 1
  = mkC (/ 2 * ln (q * q + a * a) - / 2 * ln (p * p + a * a))
        (atan (q / a) - atan (p / a)).
Proof.
  intros a p q Ha Hf; unfold pathint; apply Ceq.
  - rewrite Re_Cintf.
    rewrite (FTC_antideriv _ (GReg a p q) 0 1 Rle_0_1
               (fun x _ => proj1 Hf x) (cont_RI _ (proj1 Hf) 0 1)).
    + unfold GReg, Den; rewrite !Ld_0, !Ld_1; cbn [Re Im]; ring.
    + split; [ | lra ]; intros x _.
      exists (exist (fun l => derivable_pt_lim (GReg a p q) x l)
               (Ld p q x * (q - p) / Den a p q x) (GReg_deriv a p q x Ha)).
      unfold derive_pt; simpl; apply vchord_Re; exact Ha.
  - rewrite Im_Cintf.
    rewrite (FTC_antideriv _ (GImv a p q) 0 1 Rle_0_1
               (fun x _ => proj2 Hf x) (cont_RI _ (proj2 Hf) 0 1)).
    + unfold GImv, Ginng; rewrite Ld_0, Ld_1; cbn [Re Im]; ring.
    + split; [ | lra ]; intros x _.
      exists (exist (fun l => derivable_pt_lim (GImv a p q) x l)
               (a * (q - p) / Den a p q x) (GImv_deriv a p q x Ha)).
      unfold derive_pt; simpl; apply vchord_Im; exact Ha.
Qed.

(* ----------------------------------------------------------------- *)
(*  HORIZONTAL segment  mkC p b → mkC q b  (constant Im = b):           *)
(*    Im antiderivative −atan(Ld/b).                                   *)
(* ----------------------------------------------------------------- *)

Definition GImh (b p q s : R) : R := - atan (Ginng b p q s).

Lemma GImh_deriv : forall b p q s, b <> 0 ->
  derivable_pt_lim (GImh b p q) s (- b * (q - p) / Den b p q s).
Proof.
  intros b p q s Hb.
  assert (Hcomp : derivable_pt_lim (fun s => atan (Ginng b p q s)) s
                    (/ (1 + (Ginng b p q s) ^ 2) * ((q - p) / b))).
  { apply (derivable_pt_lim_comp (Ginng b p q) atan s
             ((q - p) / b) (/ (1 + (Ginng b p q s) ^ 2))).
    - apply Ginng_deriv; exact Hb.
    - apply derivable_pt_lim_atan. }
  unfold GImh.
  assert (HN : Den b p q s <> 0) by (apply Rgt_not_eq, Den_pos; exact Hb).
  assert (Hbb : b * b <> 0) by (apply Rmult_integral_contrapositive_currified; exact Hb).
  replace (- b * (q - p) / Den b p q s)
    with (- (/ (1 + (Ginng b p q s) ^ 2) * ((q - p) / b))).
  2:{ rewrite (one_plus_innerg b p q s Hb); field; repeat split; assumption. }
  exact (derivable_pt_lim_opp (fun s => atan (Ginng b p q s)) s
           (/ (1 + (Ginng b p q s) ^ 2) * ((q - p) / b)) Hcomp).
Qed.

Lemma segh : forall p q b s, seg (mkC p b) (mkC q b) s = mkC (Ld p q s) b.
Proof. intros; unfold seg, Ld, Cadd, Cmul, Cminus, RtoC; apply Ceq; cbn; ring. Qed.
Lemma segh' : forall p q b s, seg' (mkC p b) (mkC q b) s = mkC (q - p) 0.
Proof. intros; unfold seg', Cminus; apply Ceq; cbn; ring. Qed.
Lemma Cnorm2h : forall p q b s, Cnorm2 (mkC (Ld p q s) b) = Den b p q s.
Proof. intros; unfold Cnorm2, Den; cbn [Re Im]; ring. Qed.

Lemma hchord_Re : forall p q b s, b <> 0 ->
  Re (Cmul (Cinv (seg (mkC p b) (mkC q b) s)) (seg' (mkC p b) (mkC q b) s))
  = Ld p q s * (q - p) / Den b p q s.
Proof.
  intros p q b s Hb; rewrite segh, segh'.
  unfold Cmul, Cinv; cbn [Re Im]; rewrite !Cnorm2h.
  field; apply Rgt_not_eq, Den_pos; exact Hb.
Qed.
Lemma hchord_Im : forall p q b s, b <> 0 ->
  Im (Cmul (Cinv (seg (mkC p b) (mkC q b) s)) (seg' (mkC p b) (mkC q b) s))
  = - b * (q - p) / Den b p q s.
Proof.
  intros p q b s Hb; rewrite segh, segh'.
  unfold Cmul, Cinv; cbn [Re Im]; rewrite !Cnorm2h.
  field; apply Rgt_not_eq, Den_pos; exact Hb.
Qed.

Lemma hseg_winding : forall (p q b : R) (Hb : b <> 0)
  (Hf : Ccont (fun u => Cmul (Cinv (seg (mkC p b) (mkC q b) u))
                             (seg' (mkC p b) (mkC q b) u))),
  pathint (seg (mkC p b) (mkC q b)) (seg' (mkC p b) (mkC q b)) Cinv Hf 0 1
  = mkC (/ 2 * ln (q * q + b * b) - / 2 * ln (p * p + b * b))
        (- (atan (q / b) - atan (p / b))).
Proof.
  intros p q b Hb Hf; unfold pathint; apply Ceq.
  - rewrite Re_Cintf.
    rewrite (FTC_antideriv _ (GReg b p q) 0 1 Rle_0_1
               (fun x _ => proj1 Hf x) (cont_RI _ (proj1 Hf) 0 1)).
    + unfold GReg, Den; rewrite !Ld_0, !Ld_1; cbn [Re Im]; ring.
    + split; [ | lra ]; intros x _.
      exists (exist (fun l => derivable_pt_lim (GReg b p q) x l)
               (Ld p q x * (q - p) / Den b p q x) (GReg_deriv b p q x Hb)).
      unfold derive_pt; simpl; apply hchord_Re; exact Hb.
  - rewrite Im_Cintf.
    rewrite (FTC_antideriv _ (GImh b p q) 0 1 Rle_0_1
               (fun x _ => proj2 Hf x) (cont_RI _ (proj2 Hf) 0 1)).
    + unfold GImh, Ginng; rewrite Ld_0, Ld_1; cbn [Re Im]; ring.
    + split; [ | lra ]; intros x _.
      exists (exist (fun l => derivable_pt_lim (GImh b p q) x l)
               (- b * (q - p) / Den b p q x) (GImh_deriv b p q x Hb)).
      unfold derive_pt; simpl; apply hchord_Im; exact Hb.
Qed.

(* ----------------------------------------------------------------- *)
(*  atan complement:  atan x + atan (1/x) = π/2  for x>0               *)
(* ----------------------------------------------------------------- *)

Lemma atan_compl : forall x, 0 < x -> atan x + atan (/ x) = PI / 2.
Proof. intros x Hx; pose proof (atan_inv x Hx); lra. Qed.

(* ================================================================= *)
(*  THE RECTANGLE WINDING NUMBER:  ∮_rect dz/z = 2πi.                   *)
(*  Corners  c−iT → c+iT → −U+iT → −U−iT → (back).                      *)
(* ================================================================= *)

Theorem rect_winding : forall (c U T : R), 0 < c -> 0 < U -> 0 < T ->
  forall (Hf1 : Ccont (fun u => Cmul (Cinv (seg (mkC c (- T)) (mkC c T) u))
                                     (seg' (mkC c (- T)) (mkC c T) u)))
         (Hf2 : Ccont (fun u => Cmul (Cinv (seg (mkC c T) (mkC (- U) T) u))
                                     (seg' (mkC c T) (mkC (- U) T) u)))
         (Hf3 : Ccont (fun u => Cmul (Cinv (seg (mkC (- U) T) (mkC (- U) (- T)) u))
                                     (seg' (mkC (- U) T) (mkC (- U) (- T)) u)))
         (Hf4 : Ccont (fun u => Cmul (Cinv (seg (mkC (- U) (- T)) (mkC c (- T)) u))
                                     (seg' (mkC (- U) (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T))
                (seg' (mkC c (- T)) (mkC c T)) Cinv Hf1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC (- U) T))
                 (seg' (mkC c T) (mkC (- U) T)) Cinv Hf2 0 1)
  (Cadd (pathint (seg (mkC (- U) T) (mkC (- U) (- T)))
                 (seg' (mkC (- U) T) (mkC (- U) (- T))) Cinv Hf3 0 1)
        (pathint (seg (mkC (- U) (- T)) (mkC c (- T)))
                 (seg' (mkC (- U) (- T)) (mkC c (- T))) Cinv Hf4 0 1)))
  = mkC 0 (2 * PI).
Proof.
  intros c U T Hc HU HT Hf1 Hf2 Hf3 Hf4.
  assert (Hc0 : c <> 0) by lra.
  assert (HU0 : - U <> 0) by lra.
  assert (HT0 : T <> 0) by lra.
  assert (HnT0 : - T <> 0) by lra.
  (* edge 1 & 3 are vertical (const Re), edge 2 & 4 horizontal (const Im) *)
  rewrite (vseg_winding c (- T) T Hc0 Hf1).
  rewrite (hseg_winding c (- U) T HT0 Hf2).
  rewrite (vseg_winding (- U) T (- T) HU0 Hf3).
  rewrite (hseg_winding (- U) c (- T) HnT0 Hf4).
  unfold Cadd; apply Ceq; cbn [Re Im].
  - (* Re parts telescope to 0 *)
    replace ((- T) * (- T)) with (T * T) by ring.
    replace ((- U) * (- U)) with (U * U) by ring.
    ring.
  - (* Im parts sum to 2π *)
    pose proof (atan_compl (T / c) (Rdiv_lt_0_compat T c HT Hc)) as H1.
    pose proof (atan_compl (U / T) (Rdiv_lt_0_compat U T HU HT)) as H2.
    replace (/ (T / c)) with (c / T) in H1 by (field; lra).
    replace (/ (U / T)) with (T / U) in H2 by (field; lra).
    replace (- T / c) with (- (T / c)) in * by (field; lra).
    replace (- U / T) with (- (U / T)) in * by (field; lra).
    replace (T / - U) with (- (T / U)) in * by (field; lra).
    replace (c / - T) with (- (c / T)) in * by (field; lra).
    replace (- T / - U) with (T / U) in * by (field; lra).
    replace (- U / - T) with (U / T) in * by (field; lra).
    rewrite !atan_opp.
    lra.
Qed.

Print Assumptions rect_winding.

(* ================================================================= *)
(*  END RectWinding.v  —  ∮_rect dz/z = 2πi, plus the reusable general   *)
(*  vertical/horizontal segment integrals vseg_winding / hseg_winding.  *)
(* ================================================================= *)
