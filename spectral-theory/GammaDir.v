(* ================================================================= *)
(*  GammaDir.v  --  the direction of Gamma as an explicit arctan sum. *)
(*                                                                    *)
(*  From the Weierstrass product (GammaCWeierstrass)                  *)
(*     Pc z = z e^{gamma z} prod_{k>=1} (1 + z/k) e^{-z/k},           *)
(*     GammaC z * Pc z = 1        (GammaCNe0, via CWalk.reach)        *)
(*  and CPolarDir (angles add), the direction of Pc z is the sum      *)
(*                                                                    *)
(*     atan(Im z/Re z) + gamma Im z                                   *)
(*        + sum_{k>=1} [ atan( Im z / (k + Re z) ) - Im z / k ].      *)
(*                                                                    *)
(*  Each summand is O(1/k^2) -- the leading Im z / k cancels -- which  *)
(*  is why the DIRECTION converges much faster than the MODULUS of    *)
(*  the same product (whose deviations are only O(|z|^2/k^2)).  That   *)
(*  gap is the whole point: certifying sign(Z) needs the direction of  *)
(*  Gamma and never its magnitude.                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Ratan Lra Lia.
Require Import ComplexField Cmodulus EulerFormula CexpFull CSeries CInfProd
        CPolarDir GammaC GammaCWeierstrass EulerMascheroni.
Open Scope R_scope.

(* ---- atan on the nonnegative axis:  0 <= u - atan u <= u^3 ---- *)

Lemma atan_sandwich : forall u, 0 <= u -> 0 <= u - atan u <= u ^ 3.
Proof.
  intros u Hu. destruct (Rle_lt_or_eq_dec 0 u Hu) as [Hpos | Heq].
  - set (f := fun x : R => x - atan x).
    set (f' := fun x : R => 1 - / (1 + x ^ 2)).
    assert (Hd : forall c, 0 <= c <= u -> derivable_pt_lim f c (f' c)).
    { intros c _. unfold f, f'.
      apply (derivable_pt_lim_minus (fun x : R => x) atan c 1 (/ (1 + c ^ 2)));
        [ apply derivable_pt_lim_id | apply derivable_pt_lim_atan ]. }
    destruct (MVT_cor2 f f' 0 u Hpos Hd) as [c [Hfc [Hc0 Hcu]]].
    assert (Hf0 : f 0 = 0) by (unfold f; rewrite atan_0; ring).
    rewrite Hf0 in Hfc.
    assert (Hden : 0 < 1 + c ^ 2) by nra.
    assert (Hlo : 0 <= f' c).
    { unfold f'. assert (/ (1 + c ^ 2) <= 1).
      { rewrite <- Rinv_1. apply Rinv_le_contravar; nra. } lra. }
    assert (Hhi : f' c <= c ^ 2).
    { unfold f'.
      assert (H : 1 - / (1 + c ^ 2) = c ^ 2 / (1 + c ^ 2)) by (field; lra).
      rewrite H.
      apply Rmult_le_reg_r with (1 + c ^ 2); [ lra | ].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    unfold f in Hfc.
    assert (Hfc' : u - atan u = f' c * u).
    { replace (u - atan u) with (u - atan u - 0) by ring.
      rewrite Hfc. ring. }
    split.
    + rewrite Hfc'. apply Rmult_le_pos; lra.
    + rewrite Hfc'. replace (u ^ 3) with (u ^ 2 * u) by ring.
      apply Rmult_le_compat_r; [ lra | nra ].
  - rewrite <- Heq. rewrite atan_0. simpl. lra.
Qed.

(* ---- the angle contributed by the k-th Weierstrass factor ---- *)

Definition wang (z : C) (k : nat) : R :=
  match k with
  | O => 0
  | S m => atan (Im z / INR (S m) / (1 + Re z / INR (S m))) - Im z / INR (S m)
  end.

Lemma dir_wcf : forall z k, 0 < Re z -> PosDir (wang z k) (wcf z k).
Proof.
  intros z k Hz. destruct k as [| m].
  - cbn [wcf wang]. apply PosDir_C1.
  - assert (Hk : 0 < INR (S m)) by (apply lt_0_INR; lia).
    cbn [wcf wang].
    set (k := INR (S m)) in *.
    assert (Hkne : k <> 0) by lra.
    assert (E0 : Cdiv z (RtoC k) = mkC (Re z / k) (Im z / k)).
    { unfold Cdiv. rewrite (Cinv_RtoC k Hkne).
      unfold Cmul, RtoC; apply Ceq; cbn [Re Im]; field; exact Hkne. }
    assert (E1 : Cadd C1 (Cdiv z (RtoC k)) = mkC (1 + Re z / k) (Im z / k)).
    { rewrite E0. unfold Cadd, C1; apply Ceq; cbn [Re Im]; ring. }
    assert (E2 : Im (Copp (Cdiv z (RtoC k))) = - (Im z / k)).
    { rewrite E0. unfold Copp; cbn [Re Im]; ring. }
    replace (atan (Im z / k / (1 + Re z / k)) - Im z / k)
      with (atan (Im z / k / (1 + Re z / k)) + - (Im z / k)) by ring.
    apply PosDir_mul.
    + rewrite E1. apply dir_atan.
      assert (0 < Re z / k) by (apply Rdiv_lt_0_compat; assumption). lra.
    + rewrite <- E2. apply dir_Cexpf.
Qed.

Definition wangsum (z : C) (N : nat) : R := sum_f_R0 (wang z) N.

Lemma dir_Pprod : forall z N, 0 < Re z ->
  PosDir (wangsum z N) (Pprod (wcf z) N).
Proof.
  intros z N Hz. induction N as [| N IH].
  - cbn [Pprod]. unfold wangsum; cbn [sum_f_R0]. apply dir_wcf; exact Hz.
  - rewrite Pprod_S. unfold wangsum. rewrite tech5.
    apply PosDir_mul; [ exact IH | apply dir_wcf; exact Hz ].
Qed.

(* ================================================================= *)
(*  Convergence of the angle series.                                  *)
(*  The k-th angle is O(1/k^2): the leading Im z / k cancels between   *)
(*  atan(Im z/(k+Re z)) and the exponential factor's -Im z/k.  This is *)
(*  a strictly better rate than the product's own deviations, which    *)
(*  are only O(|z|^2/k^2) -- the direction converges faster than the   *)
(*  modulus.                                                          *)
(* ================================================================= *)

Lemma div_nonneg : forall a b, 0 <= a -> 0 < b -> 0 <= a / b.
Proof.
  intros a b Ha Hb. unfold Rdiv. apply Rmult_le_pos;
    [ exact Ha | left; apply Rinv_0_lt_compat; exact Hb ].
Qed.

Definition Kang (z : C) : R := Re z * Im z + Im z ^ 3.

Lemma Kang_nonneg : forall z, 0 < Re z -> 0 <= Im z -> 0 <= Kang z.
Proof.
  intros z Hx Hy. unfold Kang. nra.
Qed.

Lemma wang_bound : forall z m, 0 < Re z -> 0 <= Im z ->
  0 <= - wang z (S m) <= Kang z / INR (S m) ^ 2.
Proof.
  intros z m Hx Hy.
  assert (Hk1 : 1 <= INR (S m)) by (rewrite S_INR; pose proof (pos_INR m); lra).
  set (x := Re z) in *. set (y := Im z) in *. set (k := INR (S m)) in *.
  assert (Hk : 0 < k) by lra.
  set (v := y / k). set (d := 1 + x / k). set (u := v / d).
  assert (Hxk : 0 < x / k) by (apply Rdiv_lt_0_compat; assumption).
  assert (Hd : 1 <= d) by (unfold d; lra).
  assert (Hd0 : 0 < d) by lra.
  assert (Hv : 0 <= v) by (unfold v; apply div_nonneg; lra).
  assert (Hu0 : 0 <= u) by (unfold u; apply div_nonneg; lra).
  assert (Hw : wang z (S m) = atan u - v).
  { cbn [wang]. unfold u, v, d, x, y, k. reflexivity. }
  assert (Hsplit : - wang z (S m) = (v - u) + (u - atan u)) by (rewrite Hw; ring).
  (* first piece *)
  assert (Hvu : v - u = v * (d - 1) / d) by (unfold u; field; lra).
  assert (Hd1 : d - 1 = x / k) by (unfold d; ring).
  assert (B1a : 0 <= v - u).
  { rewrite Hvu, Hd1. apply div_nonneg; [ nra | lra ]. }
  assert (B1b : v - u <= x * y / k ^ 2).
  { rewrite Hvu, Hd1.
    assert (Hvx : 0 <= v * (x / k)) by nra.
    assert (Hle : v * (x / k) / d <= v * (x / k)).
    { apply Rmult_le_reg_r with d; [ lra | ].
      unfold Rdiv at 1. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    assert (Heq : v * (x / k) = x * y / k ^ 2) by (unfold v; field; lra).
    lra. }
  (* second piece *)
  destruct (atan_sandwich u Hu0) as [B2a B2b].
  assert (Huv : u <= v).
  { assert (Hud : u * d = v) by (unfold u; field; lra). nra. }
  assert (B2c : u ^ 3 <= y ^ 3 / k ^ 2).
  { assert (Hu2 : 0 <= u ^ 2) by (apply pow_le; lra).
    assert (Hc1 : u ^ 3 <= u ^ 2 * v) by nra.
    assert (Hv2 : u ^ 2 <= v ^ 2) by nra.
    assert (Hc2 : u ^ 2 * v <= v ^ 3).
    { replace (v ^ 3) with (v ^ 2 * v) by ring.
      apply Rmult_le_compat_r; [ lra | exact Hv2 ]. }
    assert (Hcube : u ^ 3 <= v ^ 3) by lra.
    assert (Hv3 : v ^ 3 = y ^ 3 * / k ^ 3) by (unfold v; field; lra).
    assert (Hk2 : 0 < k ^ 2) by (apply pow_lt; lra).
    assert (Hk23 : k ^ 2 <= k ^ 3) by (replace (k ^ 3) with (k ^ 2 * k) by ring; nra).
    assert (Hinv : / k ^ 3 <= / k ^ 2) by (apply Rinv_le_contravar; assumption).
    assert (Hy3 : 0 <= y ^ 3) by (apply pow_le; lra).
    assert (Hstep : y ^ 3 * / k ^ 3 <= y ^ 3 * / k ^ 2)
      by (apply Rmult_le_compat_l; assumption).
    unfold Rdiv. lra. }
  (* combine *)
  assert (Hsum : x * y / k ^ 2 + y ^ 3 / k ^ 2 = Kang z / k ^ 2)
    by (unfold Kang; fold x y; field; lra).
  lra.
Qed.

(* ---- summation helpers ---- *)

Lemma sum_scal_l : forall (f : nat -> R) c N,
  sum_f_R0 (fun k => c * f k) N = c * sum_f_R0 f N.
Proof. intros f c N. induction N; simpl; [ ring | rewrite IHN; ring ]. Qed.

Lemma sum_le_termwise : forall (f g : nat -> R) N,
  (forall k, f k <= g k) -> sum_f_R0 f N <= sum_f_R0 g N.
Proof.
  intros f g N H. induction N; simpl; [ apply H | pose proof (H (S N)); lra ].
Qed.

Definition negwang (z : C) (N : nat) : R := sum_f_R0 (fun k => - wang z k) N.

Lemma wangsum_neg : forall z N, wangsum z N = - negwang z N.
Proof.
  intros z N. unfold wangsum, negwang.
  induction N; simpl; [ ring | rewrite IHN; ring ].
Qed.

Lemma negwang_growing : forall z, 0 < Re z -> 0 <= Im z -> Un_growing (negwang z).
Proof.
  intros z Hx Hy n. unfold negwang. rewrite tech5.
  destruct (wang_bound z n Hx Hy) as [H _]. lra.
Qed.

Lemma negwang_ub : forall z, 0 < Re z -> 0 <= Im z -> has_ub (negwang z).
Proof.
  intros z Hx Hy. exists (2 * Kang z). intros q [i ->]. unfold negwang.
  assert (Hterm : forall k, - wang z k <= Kang z * / INR k ^ 2).
  { intro k. destruct k as [| m].
    - cbn [wang]. replace (INR 0) with 0 by reflexivity.
      replace (0 ^ 2) with 0 by ring. rewrite Rinv_0, Rmult_0_r. lra.
    - destruct (wang_bound z m Hx Hy) as [_ H]. unfold Rdiv in H. exact H. }
  eapply Rle_trans;
    [ apply (sum_le_termwise _ (fun k => Kang z * / INR k ^ 2) i Hterm) | ].
  rewrite sum_scal_l.
  pose proof (invsq_bound i) as Hb.
  pose proof (Kang_nonneg z Hx Hy) as HK.
  nra.
Qed.

(* the limiting angle of the infinite product *)
Definition Wangl (z : C) : R :=
  match Rlt_dec 0 (Re z) with
  | left h1 =>
      match Rle_dec 0 (Im z) with
      | left h2 => - proj1_sig (growing_cv (negwang z)
                      (negwang_growing z h1 h2) (negwang_ub z h1 h2))
      | right _ => 0
      end
  | right _ => 0
  end.

Lemma Wangl_cv : forall z, 0 < Re z -> 0 <= Im z -> Un_cv (wangsum z) (Wangl z).
Proof.
  intros z Hx Hy. unfold Wangl.
  destruct (Rlt_dec 0 (Re z)) as [h1|h1]; [ | lra ].
  destruct (Rle_dec 0 (Im z)) as [h2|h2]; [ | lra ].
  set (P := growing_cv (negwang z) (negwang_growing z h1 h2) (negwang_ub z h1 h2)).
  assert (HL : Un_cv (negwang z) (proj1_sig P)) by (exact (proj2_sig P)).
  apply (Un_cv_ext' (fun N => - negwang z N) (wangsum z)).
  - intro N. symmetry. apply wangsum_neg.
  - apply CV_opp. exact HL.
Qed.

(* ---- directions ---- *)

Lemma dir_self : forall z, 0 < Re z -> PosDir (atan (Im z / Re z)) z.
Proof.
  intros z Hz. destruct z as [a b]; cbn [Re Im] in *. apply dir_atan; exact Hz.
Qed.

(* The direction of the Weierstrass product, as an explicit arctan series.
   Wc z <> C0 is supplied by the exp/log bridge (GammaExpLog.Wc_ne0);
   it is a hypothesis here to keep this file independent of it. *)
Theorem dir_Wc : forall z, 0 < Re z -> 0 <= Im z -> Wc z <> C0 ->
  PosDir (Wangl z) (Wc z).
Proof.
  intros z Hx Hy Hne.
  apply (PosDir_lim (Pprod (wcf z)) (Wc z) (wangsum z) (Wangl z)).
  - apply Wc_spec.
  - apply Wangl_cv; assumption.
  - intro N. apply dir_Pprod; exact Hx.
  - exact Hne.
Qed.

(* the angle of  Pc z = z e^{gamma z} Wc z *)
Definition Pang (z : C) : R := atan (Im z / Re z) + gamma * Im z + Wangl z.

Theorem dir_Pc : forall z, 0 < Re z -> 0 <= Im z -> Wc z <> C0 ->
  PosDir (Pang z) (Pc z).
Proof.
  intros z Hx Hy Hne. unfold Pc, Pang.
  apply PosDir_mul; [ apply PosDir_mul | apply dir_Wc; assumption ].
  - apply dir_self; exact Hx.
  - assert (E : Im (Cmul (RtoC gamma) z) = gamma * Im z)
      by (unfold Cmul, RtoC; cbn [Re Im]; ring).
    rewrite <- E. apply dir_Cexpf.
Qed.

(* ================================================================= *)
(*  The tail bound: N terms suffice to within Kang z / N.             *)
(*  1/m^2 <= 1/(m-1) - 1/m telescopes, so the remainder after N terms *)
(*  is at most Kang z / N -- linear in Im z, NOT quadratic.  At        *)
(*  z = 1/4 + i t/2 this is (t/8 + t^3/8)/N ... the t^3 comes from the *)
(*  atan expansion and dominates; either way the term count needed for *)
(*  a FIXED angular accuracy is polynomial in t, not exponential.     *)
(* ================================================================= *)

Lemma negwang_mono : forall z n m, 0 < Re z -> 0 <= Im z -> (n <= m)%nat ->
  negwang z n <= negwang z m.
Proof.
  intros z n m Hx Hy Hnm. induction Hnm as [| m Hnm IH]; [ lra | ].
  pose proof (negwang_growing z Hx Hy m). lra.
Qed.

Lemma negwang_step : forall z N j, 0 < Re z -> 0 <= Im z -> (1 <= N)%nat ->
  negwang z (N + j) <= negwang z N + Kang z * (/ INR N - / INR (N + j)).
Proof.
  intros z N j Hx Hy HN.
  assert (HK : 0 <= Kang z) by (apply Kang_nonneg; assumption).
  induction j as [| j IH].
  - rewrite Nat.add_0_r. lra.
  - assert (Hstep : negwang z (N + S j) = negwang z (N + j) + - wang z (S (N + j))).
    { replace (N + S j)%nat with (S (N + j)) by lia.
      unfold negwang. rewrite tech5. reflexivity. }
    rewrite Hstep.
    destruct (wang_bound z (N + j) Hx Hy) as [_ Hb].
    (* 1/(N+j+1)^2 <= 1/(N+j) - 1/(N+j+1) *)
    assert (Hn1 : 1 <= INR (N + j)) by
      (rewrite <- (INR_1); apply le_INR; lia).
    assert (Hn2 : INR (S (N + j)) = INR (N + j) + 1) by (rewrite S_INR; reflexivity).
    assert (Htel : Kang z / INR (S (N + j)) ^ 2
                   <= Kang z * (/ INR (N + j) - / INR (S (N + j)))).
    { rewrite Hn2.
      assert (Hd : / INR (N + j) - / (INR (N + j) + 1)
                   = / (INR (N + j) * (INR (N + j) + 1))) by (field; lra).
      rewrite Hd.
      assert (Hle : / (INR (N + j) + 1) ^ 2 <= / (INR (N + j) * (INR (N + j) + 1))).
      { apply Rinv_le_contravar; nra. }
      unfold Rdiv. apply Rmult_le_compat_l; assumption. }
    assert (Heq : INR (N + S j) = INR (S (N + j)))
      by (replace (N + S j)%nat with (S (N + j)) by lia; reflexivity).
    rewrite Heq. lra.
Qed.

Theorem Wangl_tail : forall z N, 0 < Re z -> 0 <= Im z -> (1 <= N)%nat ->
  Rabs (Wangl z - wangsum z N) <= Kang z / INR N.
Proof.
  intros z N Hx Hy HN.
  assert (HK : 0 <= Kang z) by (apply Kang_nonneg; assumption).
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  (* every partial sum is below the bound *)
  assert (Hall : forall n, negwang z n <= negwang z N + Kang z / INR N).
  { intro n. destruct (Nat.le_gt_cases n N) as [Hc | Hc].
    - pose proof (negwang_mono z n N Hx Hy Hc).
      assert (0 <= Kang z / INR N) by (apply div_nonneg; lra). lra.
    - assert (Hj : n = (N + (n - N))%nat) by lia.
      rewrite Hj.
      pose proof (negwang_step z N (n - N) Hx Hy HN) as Hs.
      assert (Hpos : 0 < INR (N + (n - N))) by (apply lt_0_INR; lia).
      assert (Hinv : 0 < / INR (N + (n - N))) by (apply Rinv_0_lt_compat; exact Hpos).
      assert (Hb : Kang z * (/ INR N - / INR (N + (n - N))) <= Kang z / INR N).
      { unfold Rdiv. apply Rmult_le_compat_l; lra. }
      lra. }
  (* pass to the limit *)
  assert (Hlim : Un_cv (negwang z) (- Wangl z)).
  { apply (Un_cv_ext' (fun n => - wangsum z n) (negwang z)).
    - intro n. rewrite wangsum_neg. ring.
    - apply CV_opp. apply Wangl_cv; assumption. }
  assert (Hle : - Wangl z <= negwang z N + Kang z / INR N)
    by (apply (cv_le_ub (negwang z) (- Wangl z)); assumption).
  assert (Hge : negwang z N <= - Wangl z)
    by (apply growing_ineq; [ apply negwang_growing; assumption | exact Hlim ]).
  (* the remainder is between 0 and Kang z / N *)
  rewrite (wangsum_neg z N).
  unfold Rabs; destruct (Rcase_abs (Wangl z - - negwang z N)); lra.
Qed.

(* ================================================================= *)
(*  The SHARP tail bound.                                             *)
(*                                                                    *)
(*  Wangl_tail above degrades u^3 <= y^3/k^3 to y^3/k^2 so that both   *)
(*  pieces share one 1/k^2, which is sound but costs a whole factor    *)
(*  of N: at z = 1/4 + i t/2 it reads (t/8 + t^3/8)/N, demanding       *)
(*  ~2e5 terms at t = 26.  Keeping the cube gives                     *)
(*                                                                    *)
(*     |Wangl z - wangsum z N| <= Re z Im z / N + Im z^3 / (2 N^2)     *)
(*                             =  t/(8N) + t^3/(16 N^2)               *)
(*                                                                    *)
(*  which needs ~500 terms at t = 26 for 0.01 rad.  Two telescopes:    *)
(*  1/m^2 <= 1/(m-1) - 1/m  and  1/m^3 <= (1/2)(1/(m-1)^2 - 1/m^2).    *)
(* ================================================================= *)

Lemma wang_bound2 : forall z m, 0 < Re z -> 0 <= Im z ->
  - wang z (S m)
  <= Re z * Im z / INR (S m) ^ 2 + Im z ^ 3 / INR (S m) ^ 3.
Proof.
  intros z m Hx Hy.
  assert (Hk1 : 1 <= INR (S m)) by (rewrite S_INR; pose proof (pos_INR m); lra).
  set (x := Re z) in *. set (y := Im z) in *. set (k := INR (S m)) in *.
  assert (Hk : 0 < k) by lra.
  set (v := y / k). set (d := 1 + x / k). set (u := v / d).
  assert (Hxk : 0 < x / k) by (apply Rdiv_lt_0_compat; assumption).
  assert (Hd : 1 <= d) by (unfold d; lra).
  assert (Hd0 : 0 < d) by lra.
  assert (Hv : 0 <= v) by (unfold v; apply div_nonneg; lra).
  assert (Hu0 : 0 <= u) by (unfold u; apply div_nonneg; lra).
  assert (Hw : wang z (S m) = atan u - v).
  { cbn [wang]. unfold u, v, d, x, y, k. reflexivity. }
  assert (Hsplit : - wang z (S m) = (v - u) + (u - atan u)) by (rewrite Hw; ring).
  (* first piece, as before *)
  assert (Hvu : v - u = v * (d - 1) / d) by (unfold u; field; lra).
  assert (Hd1 : d - 1 = x / k) by (unfold d; ring).
  assert (B1 : v - u <= x * y / k ^ 2).
  { rewrite Hvu, Hd1.
    assert (Hvx : 0 <= v * (x / k)) by nra.
    assert (Hle : v * (x / k) / d <= v * (x / k)).
    { apply Rmult_le_reg_r with d; [ lra | ].
      unfold Rdiv at 1. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    assert (Heq : v * (x / k) = x * y / k ^ 2) by (unfold v; field; lra).
    lra. }
  (* second piece, keeping the cube *)
  destruct (atan_sandwich u Hu0) as [_ B2b].
  assert (Huv : u <= v).
  { assert (Hud : u * d = v) by (unfold u; field; lra). nra. }
  assert (B2 : u ^ 3 <= y ^ 3 / k ^ 3).
  { assert (Hu2 : 0 <= u ^ 2) by (apply pow_le; lra).
    assert (Hc1 : u ^ 3 <= u ^ 2 * v) by nra.
    assert (Hv2 : u ^ 2 <= v ^ 2) by nra.
    assert (Hc2 : u ^ 2 * v <= v ^ 3).
    { replace (v ^ 3) with (v ^ 2 * v) by ring.
      apply Rmult_le_compat_r; [ lra | exact Hv2 ]. }
    assert (Hv3 : v ^ 3 = y ^ 3 / k ^ 3) by (unfold v; field; lra).
    lra. }
  lra.
Qed.

Lemma negwang_step2 : forall z N j, 0 < Re z -> 0 <= Im z -> (1 <= N)%nat ->
  negwang z (N + j) <= negwang z N
    + Re z * Im z * (/ INR N - / INR (N + j))
    + Im z ^ 3 / 2 * (/ INR N ^ 2 - / INR (N + j) ^ 2).
Proof.
  intros z N j Hx Hy HN.
  assert (Hxy : 0 <= Re z * Im z) by nra.
  assert (Hy3 : 0 <= Im z ^ 3) by (apply pow_le; lra).
  induction j as [| j IH].
  - rewrite Nat.add_0_r. lra.
  - assert (Hstep : negwang z (N + S j) = negwang z (N + j) + - wang z (S (N + j))).
    { replace (N + S j)%nat with (S (N + j)) by lia.
      unfold negwang. rewrite tech5. reflexivity. }
    rewrite Hstep.
    pose proof (wang_bound2 z (N + j) Hx Hy) as Hb.
    assert (Hn1 : 1 <= INR (N + j)) by (rewrite <- INR_1; apply le_INR; lia).
    assert (Hn2 : INR (S (N + j)) = INR (N + j) + 1) by (rewrite S_INR; reflexivity).
    rewrite Hn2 in Hb.
    set (m := INR (N + j)) in *.
    assert (Hm0 : 0 < m) by lra.
    assert (T1 : / (m + 1) ^ 2 <= / m - / (m + 1)).
    { assert (E : / m - / (m + 1) = / (m * (m + 1)))
        by (field; split; apply Rgt_not_eq; lra).
      rewrite E. apply Rinv_le_contravar; nra. }
    assert (T2 : / (m + 1) ^ 3 <= / 2 * (/ m ^ 2 - / (m + 1) ^ 2)).
    { assert (Hpos : 0 < m ^ 2 * (m + 1) ^ 3) by nra.
      apply Rmult_le_reg_r with (m ^ 2 * (m + 1) ^ 3); [ exact Hpos | ].
      assert (EL : / (m + 1) ^ 3 * (m ^ 2 * (m + 1) ^ 3) = m ^ 2)
        by (field; apply Rgt_not_eq; nra).
      assert (ER : / 2 * (/ m ^ 2 - / (m + 1) ^ 2) * (m ^ 2 * (m + 1) ^ 3)
                   = / 2 * ((m + 1) ^ 3 - m ^ 2 * (m + 1)))
        by (field; split; apply Rgt_not_eq; nra).
      rewrite EL, ER. nra. }
    assert (P1 : Re z * Im z * / (m + 1) ^ 2
                 <= Re z * Im z * (/ m - / (m + 1)))
      by (apply Rmult_le_compat_l; assumption).
    assert (P2 : Im z ^ 3 * / (m + 1) ^ 3
                 <= Im z ^ 3 * (/ 2 * (/ m ^ 2 - / (m + 1) ^ 2)))
      by (apply Rmult_le_compat_l; assumption).
    assert (Heq : INR (N + S j) = m + 1).
    { replace (N + S j)%nat with (S (N + j)) by lia.
      rewrite S_INR. reflexivity. }
    rewrite Heq. unfold Rdiv in *. lra.
Qed.

Theorem Wangl_tail2 : forall z N, 0 < Re z -> 0 <= Im z -> (1 <= N)%nat ->
  Rabs (Wangl z - wangsum z N)
  <= Re z * Im z / INR N + Im z ^ 3 / 2 / INR N ^ 2.
Proof.
  intros z N Hx Hy HN.
  assert (Hxy : 0 <= Re z * Im z) by nra.
  assert (Hy3 : 0 <= Im z ^ 3) by (apply pow_le; lra).
  assert (HNpos : 0 < INR N) by (apply lt_0_INR; lia).
  assert (HN2 : 0 < INR N ^ 2) by nra.
  set (B := Re z * Im z / INR N + Im z ^ 3 / 2 / INR N ^ 2).
  assert (HB : 0 <= B).
  { unfold B. apply Rplus_le_le_0_compat.
    - apply div_nonneg; lra.
    - apply div_nonneg; [ apply div_nonneg; lra | exact HN2 ]. }
  assert (Hall : forall n, negwang z n <= negwang z N + B).
  { intro n. destruct (Nat.le_gt_cases n N) as [Hc | Hc].
    - pose proof (negwang_mono z n N Hx Hy Hc). lra.
    - assert (Hj : n = (N + (n - N))%nat) by lia.
      rewrite Hj.
      pose proof (negwang_step2 z N (n - N) Hx Hy HN) as Hs.
      assert (Hpos : 0 < INR (N + (n - N))) by (apply lt_0_INR; lia).
      assert (Ha : 0 <= / INR (N + (n - N)))
        by (left; apply Rinv_0_lt_compat; exact Hpos).
      assert (Hb : 0 <= / INR (N + (n - N)) ^ 2)
        by (left; apply Rinv_0_lt_compat; nra).
      assert (Q1 : Re z * Im z * (/ INR N - / INR (N + (n - N)))
                   <= Re z * Im z * / INR N) by nra.
      assert (Q2 : Im z ^ 3 / 2 * (/ INR N ^ 2 - / INR (N + (n - N)) ^ 2)
                   <= Im z ^ 3 / 2 * / INR N ^ 2) by nra.
      unfold B, Rdiv in *. lra. }
  assert (Hlim : Un_cv (negwang z) (- Wangl z)).
  { apply (Un_cv_ext' (fun n => - wangsum z n) (negwang z)).
    - intro n. rewrite wangsum_neg. ring.
    - apply CV_opp. apply Wangl_cv; assumption. }
  assert (Hle : - Wangl z <= negwang z N + B)
    by (apply (cv_le_ub (negwang z) (- Wangl z)); assumption).
  assert (Hge : negwang z N <= - Wangl z)
    by (apply growing_ineq; [ apply negwang_growing; assumption | exact Hlim ]).
  rewrite (wangsum_neg z N). unfold B in *.
  unfold Rabs; destruct (Rcase_abs (Wangl z - - negwang z N)); lra.
Qed.
