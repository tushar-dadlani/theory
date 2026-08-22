(* ================================================================= *)
(*  CertifiedPi.v  --  a sharp, axiom-clean decimal enclosure of PI.   *)
(*                                                                    *)
(*    PI_lower : 3.14159 <= PI                                        *)
(*    PI_upper : PI <= 3.1416                                         *)
(*                                                                    *)
(*  Prerequisite for the verified-quadrature route to exhibiting the   *)
(*  first zeta zero.  The integrand there is Psi(u) u^{-3/4}           *)
(*  cos((t/2) ln u) with Psi built from e^{-pi n^2 u}, so every        *)
(*  enclosure downstream is only as good as the enclosure of PI.       *)
(*  Measured sensitivity: perturbing PI by d shifts xir(16) by         *)
(*  3.55e-5 (d/1e-4), against a margin of 7.7e-4 -- so d = 1e-4        *)
(*  suffices and the 1e-5 proved here is comfortable.                  *)
(*                                                                    *)
(*  WHY NOT THE OBVIOUS ROUTES.                                        *)
(*   * Rtrigo_alt.cos_bound is unusable: it is stated under            *)
(*     - PI/2 <= a <= PI/2, so pinning PI by evaluating cos near PI/2  *)
(*     is circular.                                                   *)
(*   * PI_ineq (Leibniz) converges like 1/N; 1e-4 needs N ~ 10^4 real  *)
(*     terms, which cannot be evaluated to a decimal by lra.           *)
(*   * ConstructivePi.cpi is a genuine constructive real but           *)
(*     cpi_tele gives only cpi k - PI <= 2/(2k+1); 1e-4 needs a Wallis *)
(*     rational recursion 10^4 deep, whose denominators explode.       *)
(*                                                                    *)
(*  THE CHEAP ROUTE is Machin-style.  PI = 4 (atan(1/2) + atan(1/3)),  *)
(*  and the identity is EXACT, not approximate: tan(a+b) = (1/2+1/3) / *)
(*  (1 - 1/6) = 1 on the nose.  Each atan is then bracketed by its     *)
(*  alternating series, which converges geometrically (ratios 1/4 and  *)
(*  1/9) rather than like 1/N.  Eight terms apiece already give a      *)
(*  width of 1e-5 with denominators of at most ten digits, well within *)
(*  what lra handles.  Axiom-clean.                                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Ratan.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the alternating enclosure of atan on (0,1)                     *)
(* ----------------------------------------------------------------- *)
Lemma ps_atan_cv : forall x, 0 < x < 1 ->
  Un_cv (fun N => sum_f_R0 (tg_alt (Ratan_seq x)) N) (ps_atan x).
Proof.
  intros x h. unfold ps_atan.
  destruct (in_int x) as [hi | hi].
  - destruct (ps_atan_exists_1 x hi) as [v Hv]. exact Hv.
  - exfalso. apply hi. split; lra.
Qed.

Theorem atan_enclose : forall x N, 0 < x < 1 ->
  sum_f_R0 (tg_alt (Ratan_seq x)) (S (2 * N)) <= atan x
  <= sum_f_R0 (tg_alt (Ratan_seq x)) (2 * N).
Proof.
  intros x N h.
  rewrite (atan_eq_ps_atan x h).
  apply alternated_series_ineq.
  - apply Ratan_seq_decreasing; lra.
  - apply Ratan_seq_converging; lra.
  - apply ps_atan_cv; exact h.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the Machin identity, exactly                                   *)
(* ----------------------------------------------------------------- *)
Lemma atan_pos_lt_quarter : forall x, 0 < x < 1 -> 0 < atan x < PI / 4.
Proof.
  intros x h. split.
  - rewrite <- atan_0. apply atan_increasing; lra.
  - rewrite <- atan_1. apply atan_increasing; lra.
Qed.

Lemma cos_atan_ne0 : forall x, cos (atan x) <> 0.
Proof.
  intro x. assert (H := atan_bound x).
  assert (0 < cos (atan x)) by (apply cos_gt_0; lra). lra.
Qed.

Theorem machin : atan (/ 2) + atan (/ 3) = PI / 4.
Proof.
  pose proof PI_RGT_0 as HPI.
  assert (Ha := atan_pos_lt_quarter (/ 2) ltac:(lra)).
  assert (Hb := atan_pos_lt_quarter (/ 3) ltac:(lra)).
  assert (Hsum : - PI / 2 < atan (/ 2) + atan (/ 3) < PI / 2) by lra.
  assert (Hcs : 0 < cos (atan (/ 2) + atan (/ 3)))
    by (apply cos_gt_0; lra).
  (* tan of the sum is exactly 1 *)
  assert (Htp : tan (atan (/ 2) + atan (/ 3)) = 1).
  { rewrite tan_plus.
    - rewrite !tan_atan. field.
    - apply cos_atan_ne0.
    - apply cos_atan_ne0.
    - lra.
    - rewrite !tan_atan. lra. }
  (* and tan (PI/4) = 1 *)
  assert (Hq : tan (PI / 4) = 1) by (rewrite <- atan_1, tan_atan; reflexivity).
  apply tan_inj; [ exact Hsum | lra | rewrite Htp, Hq; reflexivity ].
Qed.

Corollary PI_machin : PI = 4 * (atan (/ 2) + atan (/ 3)).
Proof. rewrite machin. field. Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the decimals, at eight terms apiece                            *)
(* ----------------------------------------------------------------- *)
(*  N = 3 gives sum indices S (2*3) = 7 (lower) and 2*3 = 6 (upper).   *)
(*  Exact partial sums:                                                *)
(*    atan(1/2) in [0.4636472421, 0.4636492766]   (width 2.0e-6)       *)
(*    atan(1/3) in [0.3217505540, 0.3217505586]   (width 4.6e-9)       *)
(*  so 4 * (sum + sum) lands in [3.1415911, 3.1415994].                *)
(* ----------------------------------------------------------------- *)
Lemma atan_half_bounds :
  sum_f_R0 (tg_alt (Ratan_seq (/ 2))) 7 <= atan (/ 2)
  <= sum_f_R0 (tg_alt (Ratan_seq (/ 2))) 6.
Proof. exact (atan_enclose (/ 2) 3 ltac:(lra)). Qed.

Lemma atan_third_bounds :
  sum_f_R0 (tg_alt (Ratan_seq (/ 3))) 7 <= atan (/ 3)
  <= sum_f_R0 (tg_alt (Ratan_seq (/ 3))) 6.
Proof. exact (atan_enclose (/ 3) 3 ltac:(lra)). Qed.

Lemma sum_half_lo : 0.4636472 <= sum_f_R0 (tg_alt (Ratan_seq (/ 2))) 7.
Proof. unfold tg_alt, Ratan_seq; simpl; lra. Qed.

Lemma sum_half_hi : sum_f_R0 (tg_alt (Ratan_seq (/ 2))) 6 <= 0.4636493.
Proof. unfold tg_alt, Ratan_seq; simpl; lra. Qed.

Lemma sum_third_lo : 0.3217505 <= sum_f_R0 (tg_alt (Ratan_seq (/ 3))) 7.
Proof. unfold tg_alt, Ratan_seq; simpl; lra. Qed.

Lemma sum_third_hi : sum_f_R0 (tg_alt (Ratan_seq (/ 3))) 6 <= 0.3217506.
Proof. unfold tg_alt, Ratan_seq; simpl; lra. Qed.

Theorem PI_lower : 3.14159 <= PI.
Proof.
  rewrite PI_machin.
  destruct atan_half_bounds as [Hl2 _].
  destruct atan_third_bounds as [Hl3 _].
  pose proof sum_half_lo. pose proof sum_third_lo. lra.
Qed.

Theorem PI_upper : PI <= 3.1416.
Proof.
  rewrite PI_machin.
  destruct atan_half_bounds as [_ Hu2].
  destruct atan_third_bounds as [_ Hu3].
  pose proof sum_half_hi. pose proof sum_third_hi. lra.
Qed.

Corollary PI_enclosure : 3.14159 <= PI <= 3.1416.
Proof. split; [ apply PI_lower | apply PI_upper ]. Qed.

Print Assumptions machin.
Print Assumptions PI_enclosure.
