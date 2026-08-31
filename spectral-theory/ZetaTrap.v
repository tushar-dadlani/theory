(* ================================================================= *)
(*  ZetaTrap.v  --  the trapezoid defect for x^{-s}.                  *)
(*                                                                    *)
(*  CZeta represents zeta by the FIRST-order Euler-Maclaurin defect    *)
(*      gtermC s n = g(n+1) - [G(n+2) - G(n+1)],   g = x^{-s},        *)
(*  whose terms are O(|s| n^{-Re s-1}).  On the critical line at       *)
(*  t = 26 that tail needs ~7e6 terms for 1e-2 -- unusable.           *)
(*                                                                    *)
(*  Replacing the left endpoint by the TRAPEZOID,                     *)
(*      htermC s n = (g(n+1)+g(n+2))/2 - [G(n+2) - G(n+1)],           *)
(*  makes each term O(|s||s+1| n^{-Re s-2}), and the difference        *)
(*  telescopes, so nothing is lost.  ~250 terms then suffice.         *)
(*                                                                    *)
(*  No integration theory is needed: GC is already the closed-form     *)
(*  antiderivative of gC, so the defect is bounded by differentiating  *)
(*  twice and applying SimpsonQuad.mvt_sandwich twice.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase CSeries CZetaTerm
        SimpsonQuad.
Open Scope R_scope.

(* ---- the second derivative of  x |-> x^{-s}  ---- *)

Definition gd2C (s : C) (x : R) : C :=
  Cmul (Cmul (Cminus (Copp s) C1) (Cpw x (Cminus (Cminus (Copp s) C1) C1)))
       (Copp s).

Lemma Regd_deriv : forall s x, 0 < x ->
  derivable_pt_lim (fun t => Re (gderivC s t)) x (Re (gd2C s x)).
Proof.
  intros s x Hx. unfold gderivC, gd2C.
  assert (E : (fun t => Re (Cmul (Copp s) (Cpw t (Cminus (Copp s) C1))))
              = (fun t => Re (Cmul (Cpw t (Cminus (Copp s) C1)) (Copp s)))).
  { apply functional_extensionality. intro t. f_equal. ring. }
  rewrite E. apply Re_Cmul_deriv. exact Hx.
Qed.

Lemma Imgd_deriv : forall s x, 0 < x ->
  derivable_pt_lim (fun t => Im (gderivC s t)) x (Im (gd2C s x)).
Proof.
  intros s x Hx. unfold gderivC, gd2C.
  assert (E : (fun t => Im (Cmul (Copp s) (Cpw t (Cminus (Copp s) C1))))
              = (fun t => Im (Cmul (Cpw t (Cminus (Copp s) C1)) (Copp s)))).
  { apply functional_extensionality. intro t. f_equal. ring. }
  rewrite E. apply Im_Cmul_deriv. exact Hx.
Qed.

Lemma Cmod_gd2C : forall s x,
  Cmod (gd2C s x) = Cmod s * Cmod (Cadd s C1) * Rpower x (- Re s - 2).
Proof.
  intros s x. unfold gd2C. rewrite Cmod_mul, Cmod_wCpw, Cmod_opp.
  assert (E1 : Cmod (Cminus (Copp s) C1) = Cmod (Cadd s C1)).
  { replace (Cminus (Copp s) C1) with (Copp (Cadd s C1)) by ring.
    apply Cmod_opp. }
  assert (E2 : Re (Cminus (Copp s) C1) - 1 = - Re s - 2)
    by (unfold Cminus, Cadd, Copp, C1; cbn [Re]; ring).
  rewrite E1, E2. ring.
Qed.

(* ---- derivative wrappers in plain lambda form ---- *)

Lemma d_plus' : forall f g x lf lg,
  derivable_pt_lim f x lf -> derivable_pt_lim g x lg ->
  derivable_pt_lim (fun y => f y + g y) x (lf + lg).
Proof.
  intros f g x lf lg H1 H2.
  pose proof (derivable_pt_lim_plus f g x lf lg H1 H2) as H.
  unfold plus_fct in H. exact H.
Qed.

Lemma d_minus' : forall f g x lf lg,
  derivable_pt_lim f x lf -> derivable_pt_lim g x lg ->
  derivable_pt_lim (fun y => f y - g y) x (lf - lg).
Proof.
  intros f g x lf lg H1 H2.
  pose proof (derivable_pt_lim_minus f g x lf lg H1 H2) as H.
  unfold minus_fct in H. exact H.
Qed.

Lemma d_mult' : forall f g x lf lg,
  derivable_pt_lim f x lf -> derivable_pt_lim g x lg ->
  derivable_pt_lim (fun y => f y * g y) x (lf * g x + f x * lg).
Proof.
  intros f g x lf lg H1 H2.
  pose proof (derivable_pt_lim_mult f g x lf lg H1 H2) as H.
  unfold mult_fct in H. exact H.
Qed.

Lemma d_shift' : forall (u : R -> R) (l a h : R),
  derivable_pt_lim u (a + h) l -> derivable_pt_lim (fun v => u (a + v)) h l.
Proof.
  intros u l a h H.
  assert (Haff : derivable_pt_lim (fun v => a + v) h 1).
  { replace 1 with (0 + 1) by ring.
    apply (d_plus' (fun _ : R => a) (fun v : R => v) h 0 1);
      [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ]. }
  pose proof (derivable_pt_lim_comp (fun v => a + v) u h 1 l Haff H) as Hc.
  unfold comp in Hc; cbv beta in Hc.
  replace l with (l * 1) by ring. exact Hc.
Qed.

Lemma d_half' : forall h, derivable_pt_lim (fun u : R => u / 2) h (/ 2).
Proof.
  intro h.
  pose proof (d_mult' (fun u : R => u) (fun _ : R => / 2) h 1 0
                (derivable_pt_lim_id h) (derivable_pt_lim_const (/ 2) h)) as H.
  cbv beta in H.
  assert (E : 1 * / 2 + h * 0 = / 2) by field.
  rewrite E in H. unfold Rdiv. exact H.
Qed.

Lemma d_cpow : forall c n x,
  derivable_pt_lim (fun h : R => c * h ^ n) x (c * (INR n * x ^ Init.Nat.pred n)).
Proof.
  intros c n x.
  pose proof (d_mult' (fun _ : R => c) (fun h : R => h ^ n) x 0
                (INR n * x ^ Init.Nat.pred n)
                (derivable_pt_lim_const c x) (derivable_pt_lim_pow x n)) as H.
  cbv beta in H.
  replace (c * (INR n * x ^ Init.Nat.pred n))
    with (0 * x ^ n + c * (INR n * x ^ Init.Nat.pred n)) by ring.
  exact H.
Qed.

(* ---- the real trapezoid defect ---- *)

Section Trap.
Variable f0 f1 f2 F0 : R -> R.
Variable a M : R.
Hypothesis HM : 0 <= M.
Hypothesis HF0 : forall x, a <= x <= a + 1 -> derivable_pt_lim F0 x (f0 x).
Hypothesis Hf0 : forall x, a <= x <= a + 1 -> derivable_pt_lim f0 x (f1 x).
Hypothesis Hf1 : forall x, a <= x <= a + 1 -> derivable_pt_lim f1 x (f2 x).
Hypothesis Hf2 : forall x, a <= x <= a + 1 -> Rabs (f2 x) <= M.

Let Fh := fun h : R => F0 (a + h) - F0 a - h / 2 * (f0 a + f0 (a + h)).
Let Fd := fun h : R => / 2 * (f0 (a + h) - f0 a) - h / 2 * f1 (a + h).

Lemma trap_d1 : forall h, 0 <= h <= 1 -> derivable_pt_lim Fh h (Fd h).
Proof.
  intros h Hh. assert (Hx : a <= a + h <= a + 1) by lra.
  unfold Fh, Fd.
  assert (DA : derivable_pt_lim (fun v => F0 (a + v)) h (f0 (a + h)))
    by (apply d_shift', HF0; exact Hx).
  assert (DC : derivable_pt_lim (fun v => f0 a + f0 (a + v)) h (0 + f1 (a + h))).
  { apply (d_plus' (fun _ : R => f0 a) (fun v : R => f0 (a + v)) h 0 (f1 (a + h)));
      [ apply derivable_pt_lim_const | apply d_shift', Hf0; exact Hx ]. }
  assert (DP : derivable_pt_lim (fun v => v / 2 * (f0 a + f0 (a + v))) h
                 (/ 2 * (f0 a + f0 (a + h)) + h / 2 * (0 + f1 (a + h))))
    by (apply (d_mult' (fun v : R => v / 2) (fun v : R => f0 a + f0 (a + v)) h
                 (/ 2) (0 + f1 (a + h))); [ apply d_half' | exact DC ]).
  assert (DS : derivable_pt_lim (fun v => F0 (a + v) - F0 a) h (f0 (a + h) - 0))
    by (apply (d_minus' (fun v : R => F0 (a + v)) (fun _ : R => F0 a) h
                 (f0 (a + h)) 0); [ exact DA | apply derivable_pt_lim_const ]).
  pose proof (d_minus' _ _ _ _ _ DS DP) as D.
  replace (/ 2 * (f0 (a + h) - f0 a) - h / 2 * f1 (a + h))
    with (f0 (a + h) - 0
          - (/ 2 * (f0 a + f0 (a + h)) + h / 2 * (0 + f1 (a + h)))) by field.
  exact D.
Qed.

Lemma trap_d2 : forall h, 0 <= h <= 1 ->
  derivable_pt_lim Fd h (- (h / 2 * f2 (a + h))).
Proof.
  intros h Hh. assert (Hx : a <= a + h <= a + 1) by lra.
  unfold Fd.
  assert (DD : derivable_pt_lim (fun v => f0 (a + v) - f0 a) h (f1 (a + h) - 0)).
  { apply (d_minus' (fun v : R => f0 (a + v)) (fun _ : R => f0 a) h
             (f1 (a + h)) 0);
      [ apply d_shift', Hf0; exact Hx | apply derivable_pt_lim_const ]. }
  assert (DL : derivable_pt_lim (fun v => / 2 * (f0 (a + v) - f0 a)) h
                 (0 * (f0 (a + h) - f0 a) + / 2 * (f1 (a + h) - 0)))
    by (apply (d_mult' (fun _ : R => / 2) (fun v : R => f0 (a + v) - f0 a) h
                 0 (f1 (a + h) - 0)); [ apply derivable_pt_lim_const | exact DD ]).
  assert (DE : derivable_pt_lim (fun v => f1 (a + v)) h (f2 (a + h)))
    by (apply d_shift', Hf1; exact Hx).
  assert (DR : derivable_pt_lim (fun v => v / 2 * f1 (a + v)) h
                 (/ 2 * f1 (a + h) + h / 2 * f2 (a + h)))
    by (apply (d_mult' (fun v : R => v / 2) (fun v : R => f1 (a + v)) h
                 (/ 2) (f2 (a + h))); [ apply d_half' | exact DE ]).
  pose proof (d_minus' _ _ _ _ _ DL DR) as D.
  replace (- (h / 2 * f2 (a + h)))
    with (0 * (f0 (a + h) - f0 a) + / 2 * (f1 (a + h) - 0)
          - (/ 2 * f1 (a + h) + h / 2 * f2 (a + h))) by field.
  exact D.
Qed.

Lemma trap_bound : Rabs (Fh 1) <= M / 12.
Proof.
  assert (Dq1 : forall y, derivable_pt_lim (fun h : R => M * h ^ 2 / 4) y (M * y / 2)).
  { intro y. pose proof (d_cpow (M / 4) 2 y) as H. cbv beta in H.
    assert (E : (fun h : R => M / 4 * h ^ 2) = (fun h : R => M * h ^ 2 / 4))
      by (apply functional_extensionality; intro h; field).
    rewrite E in H.
    assert (E2 : M / 4 * (INR 2 * y ^ Init.Nat.pred 2) = M * y / 2)
      by (simpl; field).
    rewrite E2 in H. exact H. }
  assert (Dq2 : forall y, derivable_pt_lim (fun h : R => M * h ^ 3 / 12) y
                            (M * y ^ 2 / 4)).
  { intro y. pose proof (d_cpow (M / 12) 3 y) as H. cbv beta in H.
    assert (E : (fun h : R => M / 12 * h ^ 3) = (fun h : R => M * h ^ 3 / 12))
      by (apply functional_extensionality; intro h; field).
    rewrite E in H.
    assert (E2 : M / 12 * (INR 3 * y ^ Init.Nat.pred 3) = M * y ^ 2 / 4)
      by (simpl; field).
    rewrite E2 in H. exact H. }
  assert (S1 : forall x, 0 <= x <= 1 -> Rabs (Fd x) <= M * x ^ 2 / 4).
  { apply (mvt_sandwich Fd (fun h => - (h / 2 * f2 (a + h)))
             (fun h => M * h ^ 2 / 4) (fun h => M * h / 2) 0 1 0).
    - lra.
    - intros y Hy. apply trap_d2. exact Hy.
    - intros y Hy. apply Dq1.
    - unfold Fd. replace (a + 0) with a by ring. field.
    - field.
    - intros y Hy. rewrite Rabs_Ropp, Rabs_mult.
      assert (Ha1 : Rabs (y / 2) = y / 2) by (apply Rabs_right; lra).
      rewrite Ha1.
      assert (Hb1 : Rabs (f2 (a + y)) <= M) by (apply Hf2; lra).
      assert (Hb2 : 0 <= Rabs (f2 (a + y))) by apply Rabs_pos.
      nra.
    - intros y Hy. assert (Hy0 : y = 0) by lra. subst.
      replace (- (0 / 2 * f2 (a + 0))) with 0 by field.
      rewrite Rabs_R0. lra. }
  assert (S2 : forall x, 0 <= x <= 1 -> Rabs (Fh x) <= M * x ^ 3 / 12).
  { apply (mvt_sandwich Fh Fd (fun h => M * h ^ 3 / 12) (fun h => M * h ^ 2 / 4)
             0 1 0).
    - lra.
    - intros y Hy. apply trap_d1. exact Hy.
    - intros y Hy. apply Dq2.
    - unfold Fh. replace (a + 0) with a by ring. field.
    - field.
    - intros y Hy. apply S1. lra.
    - intros y Hy. assert (Hy0 : y = 0) by lra. subst.
      unfold Fd. replace (a + 0) with a by ring.
      replace (/ 2 * (f0 a - f0 a) - 0 / 2 * f1 a) with 0 by field.
      rewrite Rabs_R0. simpl. lra. }
  pose proof (S2 1 ltac:(lra)) as H.
  replace (M * 1 ^ 3 / 12) with (M / 12) in H by field. exact H.
Qed.

End Trap.

(* ================================================================= *)
(*  The complex trapezoid defect for x^{-s}.                          *)
(* ================================================================= *)

Definition htermC (s : C) (n : nat) : C :=
  Cminus (Cmul (RtoC (/ 2)) (Cadd (gC s (INR (S n))) (gC s (INR (S (S n))))))
         (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n)))).

Lemma Re_scal : forall r w, Re (Cmul (RtoC r) w) = r * Re w.
Proof. intros r w. unfold Cmul, RtoC; cbn [Re Im]; ring. Qed.

Lemma Im_scal : forall r w, Im (Cmul (RtoC r) w) = r * Im w.
Proof. intros r w. unfold Cmul, RtoC; cbn [Re Im]; ring. Qed.

Lemma Re_Cadd' : forall a b, Re (Cadd a b) = Re a + Re b.
Proof. intros a b. unfold Cadd; cbn [Re Im]; ring. Qed.

Lemma Im_Cadd' : forall a b, Im (Cadd a b) = Im a + Im b.
Proof. intros a b. unfold Cadd; cbn [Re Im]; ring. Qed.

Lemma Rabs_Re_le : forall c, Rabs (Re c) <= Cmod c.
Proof.
  intro c. eapply Rle_trans; [ | apply Rle_refl ].
  unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr (Rabs (Re c))) by apply Rabs_pos.
  apply sqrt_le_1_alt. rewrite <- Rsqr_abs. unfold Rsqr. nra.
Qed.

Lemma Rabs_Im_le : forall c, Rabs (Im c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr (Rabs (Im c))) by apply Rabs_pos.
  apply sqrt_le_1_alt. rewrite <- Rsqr_abs. unfold Rsqr. nra.
Qed.

Lemma Cmod_le_comp : forall c, Cmod c <= Rabs (Re c) + Rabs (Im c).
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr (Rabs (Re c) + Rabs (Im c)))
    by (pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)); lra).
  apply sqrt_le_1_alt. unfold Rsqr.
  pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)).
  pose proof (Rsqr_abs (Re c)) as E1; pose proof (Rsqr_abs (Im c)) as E2.
  unfold Rsqr in E1, E2. nra.
Qed.

Theorem Cmod_htermC_bound : forall s n, 0 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (htermC s n)
  <= / 6 * (Cmod s * Cmod (Cadd s C1) * Rpower (INR (S n)) (- Re s - 2)).
Proof.
  intros s n Hs Hs1.
  assert (Ha : 0 < INR (S n)) by (apply lt_0_INR; lia).
  set (a := INR (S n)) in *.
  set (M0 := Cmod s * Cmod (Cadd s C1) * Rpower a (- Re s - 2)).
  assert (HM0 : 0 <= M0).
  { unfold M0. apply Rmult_le_pos.
    - apply Rmult_le_pos; apply Cmod_nonneg.
    - unfold Rpower. left; apply exp_pos. }
  assert (Hb : INR (S (S n)) = a + 1) by (unfold a; rewrite S_INR; reflexivity).
  assert (Hmax : forall x, a <= x <= a + 1 -> Cmod (gd2C s x) <= M0).
  { intros x Hx. rewrite Cmod_gd2C. unfold M0.
    apply Rmult_le_compat_l; [ apply Rmult_le_pos; apply Cmod_nonneg | ].
    replace (- Re s - 2) with (- (Re s + 2)) by ring.
    apply Rpow_negexp_anti; [ exact Ha | lra | lra ]. }
  (* real part *)
  assert (HR : Rabs (Re (GC s (a + 1)) - Re (GC s a)
                     - 1 / 2 * (Re (gC s a) + Re (gC s (a + 1)))) <= M0 / 12).
  { apply (trap_bound (fun x => Re (gC s x)) (fun x => Re (gderivC s x))
             (fun x => Re (gd2C s x)) (fun x => Re (GC s x)) a M0).
    - intros x Hx. apply ReGC_deriv; [ lra | exact Hs1 ].
    - intros x Hx. apply RegC_deriv; lra.
    - intros x Hx. apply Regd_deriv; lra.
    - intros x Hx. eapply Rle_trans; [ apply Rabs_Re_le | apply Hmax; exact Hx ]. }
  (* imaginary part *)
  assert (HI : Rabs (Im (GC s (a + 1)) - Im (GC s a)
                     - 1 / 2 * (Im (gC s a) + Im (gC s (a + 1)))) <= M0 / 12).
  { apply (trap_bound (fun x => Im (gC s x)) (fun x => Im (gderivC s x))
             (fun x => Im (gd2C s x)) (fun x => Im (GC s x)) a M0).
    - intros x Hx. apply ImGC_deriv; [ lra | exact Hs1 ].
    - intros x Hx. apply ImgC_deriv; lra.
    - intros x Hx. apply Imgd_deriv; lra.
    - intros x Hx. eapply Rle_trans; [ apply Rabs_Im_le | apply Hmax; exact Hx ]. }
  (* assemble *)
  assert (ER : Re (htermC s n)
               = / 2 * (Re (gC s a) + Re (gC s (a + 1)))
                 - (Re (GC s (a + 1)) - Re (GC s a))).
  { unfold htermC. rewrite Hb, !Re_Cminus, Re_scal, Re_Cadd'. reflexivity. }
  assert (EI : Im (htermC s n)
               = / 2 * (Im (gC s a) + Im (gC s (a + 1)))
                 - (Im (GC s (a + 1)) - Im (GC s a))).
  { unfold htermC. rewrite Hb, !Im_Cminus, Im_scal, Im_Cadd'. reflexivity. }
  assert (HR2 : Rabs (Re (htermC s n)) <= M0 / 12).
  { rewrite ER.
    replace (/ 2 * (Re (gC s a) + Re (gC s (a + 1)))
             - (Re (GC s (a + 1)) - Re (GC s a)))
      with (- (Re (GC s (a + 1)) - Re (GC s a)
               - 1 / 2 * (Re (gC s a) + Re (gC s (a + 1))))) by field.
    rewrite Rabs_Ropp. exact HR. }
  assert (HI2 : Rabs (Im (htermC s n)) <= M0 / 12).
  { rewrite EI.
    replace (/ 2 * (Im (gC s a) + Im (gC s (a + 1)))
             - (Im (GC s (a + 1)) - Im (GC s a)))
      with (- (Im (GC s (a + 1)) - Im (GC s a)
               - 1 / 2 * (Im (gC s a) + Im (gC s (a + 1))))) by field.
    rewrite Rabs_Ropp. exact HI. }
  eapply Rle_trans; [ apply Cmod_le_comp | ].
  unfold M0 in *. lra.
Qed.
