(* ================================================================= *)
(*  BaselVieta.v  —  Σ_{k=1}^m cot²(kπ/(2m+1)) = m(2m−1)/3.          *)
(*                                                                    *)
(*  The crux of the Basel proof.  We build a minimal real-polynomial  *)
(*  layer (`list R` coefficients) with a factor theorem and the       *)
(*  "≤ deg distinct roots ⇒ zero" principle, hence VIETA's sum-of-    *)
(*  roots `Σ r_k = −a_{m−1}/a_m` (`vieta_sum`).  Applied to `Pcot m`   *)
(*  (from BaselCotPoly), whose m distinct roots are the cot²θ_k, this  *)
(*  yields `cot_sq_sum`.  No reuse — the polynomial layer is built     *)
(*  from scratch.  Over the classical `Reals` (quarantined).          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Arith FunctionalExtensionality Binomial.
Import ListNotations.
Require Import BaselCotPoly.
Local Open Scope R_scope.

Fixpoint Peval (p : list R) (x : R) : R :=
  match p with [] => 0 | c :: p' => c + x * Peval p' x end.
Fixpoint Padd (p q : list R) : list R :=
  match p, q with
  | [], _ => q | _, [] => p
  | a :: p', b :: q' => (a + b) :: Padd p' q'
  end.
Definition Pscale (s : R) (p : list R) : list R := map (Rmult s) p.
Definition Xsub (r : R) (p : list R) : list R := Padd (0 :: p) (Pscale (- r) p).

Lemma Peval_app : forall p q x, Peval (p ++ q) x = Peval p x + x ^ (length p) * Peval q x.
Proof. induction p as [|c p IH]; intros q x; cbn [Peval app length];
  [ rewrite pow_O; ring | rewrite IH, <- tech_pow_Rmult; ring ]. Qed.
Lemma Peval_add : forall p q x, Peval (Padd p q) x = Peval p x + Peval q x.
Proof. induction p as [|a p IH]; intros [|b q] x; cbn [Padd Peval]; try ring. rewrite IH; ring. Qed.
Lemma Peval_scale : forall s p x, Peval (Pscale s p) x = s * Peval p x.
Proof. intros s p x; induction p as [|c p IH]; cbn [Pscale map Peval]; [ ring | ].
  fold (Pscale s p); rewrite IH; ring. Qed.
Lemma Peval_Xsub : forall r p x, Peval (Xsub r p) x = (x - r) * Peval p x.
Proof. intros r p x; unfold Xsub; rewrite Peval_add, Peval_scale; cbn [Peval]; ring. Qed.

Lemma nth_Padd : forall p q i, nth i (Padd p q) 0 = nth i p 0 + nth i q 0.
Proof. induction p as [|a p IH]; intros [|b q] i; cbn [Padd]; try (destruct i; cbn [nth]; ring).
  destruct i as [|i]; cbn [nth]; [ ring | apply IH ]. Qed.
Lemma nth_Pscale : forall s p i, nth i (Pscale s p) 0 = s * nth i p 0.
Proof. intros s p i; unfold Pscale; replace 0 with (s * 0) at 1 by ring; rewrite map_nth; reflexivity. Qed.
Lemma length_Pscale : forall s p, length (Pscale s p) = length p.
Proof. intros; unfold Pscale; apply length_map. Qed.
Lemma length_Padd : forall p q, length (Padd p q) = Nat.max (length p) (length q).
Proof. induction p as [|a p IH]; intros [|b q]; cbn [Padd length]; try lia. rewrite IH; lia. Qed.

(* nth-with-default and trailing zero *)
Lemma nth_app_zero : forall l i, nth i (l ++ [0]) 0 = nth i l 0.
Proof. induction l as [|c l IH]; intros [|i]; cbn [app nth]; try reflexivity; [ destruct i; reflexivity | apply IH ]. Qed.
Lemma last_nth : forall l, l <> [] -> last l 0 = nth (pred (length l)) l 0.
Proof. induction l as [|c l IH]; intro H; [ congruence | ].
  destruct l as [|d l']; [ reflexivity | ].
  change (last (c :: d :: l') 0) with (last (d :: l') 0).
  change (pred (length (c :: d :: l'))) with (S (pred (length (d :: l')))).
  change (nth (S (pred (length (d :: l')))) (c :: d :: l') 0)
    with (nth (pred (length (d :: l'))) (d :: l') 0).
  apply IH; discriminate. Qed.
Lemma nth_removelast0 : forall l, last l 0 = 0 -> forall i, nth i (removelast l) 0 = nth i l 0.
Proof. intros l Hl i. destruct l as [|c l']; [ reflexivity | ].
  rewrite (app_removelast_last 0 (l:=c::l') ltac:(discriminate)) at 2. rewrite Hl.
  rewrite nth_app_zero. reflexivity. Qed.
Lemma Peval_removelast0 : forall l x, last l 0 = 0 -> Peval (removelast l) x = Peval l x.
Proof. intros l x Hl. destruct l as [|c l']; [ reflexivity | ].
  rewrite (app_removelast_last 0 (l:=c::l') ltac:(discriminate)) at 2. rewrite Hl.
  rewrite Peval_app. cbn [Peval]. ring. Qed.
Lemma length_removelast_cons : forall (l : list R), l <> [] -> length (removelast l) = pred (length l).
Proof. intros l H. rewrite (app_removelast_last 0 H) at 2. rewrite length_app. cbn [length]. lia. Qed.

(* synthetic quotient / factor theorem *)
Fixpoint quo (r : R) (p : list R) : list R :=
  match p with [] => [] | _ :: p' => Peval p' r :: quo r p' end.
Lemma length_quo : forall r p, length (quo r p) = length p.
Proof. intros r p; induction p as [|c p IH]; cbn [quo length]; [ reflexivity | rewrite IH; reflexivity ]. Qed.
Lemma quo_eval : forall r p x, Peval p x = Peval p r + (x - r) * Peval (quo r p) x.
Proof. intros r p x; induction p as [|c p IH]; cbn [quo Peval]; [ ring | rewrite IH at 1; ring ]. Qed.
Lemma last_quo : forall r p, last (quo r p) 0 = 0.
Proof. intros r p; induction p as [|c p IH]; [ reflexivity | ].
  cbn [quo]. destruct (quo r p) eqn:E.
  - assert (p = []) by (apply length_zero_iff_nil; rewrite <- (length_quo r p), E; reflexivity).
    subst p; reflexivity.
  - change (last (Peval p r :: r0 :: l) 0) with (last (r0 :: l) 0); exact IH. Qed.

(* a poly of length <= (#distinct roots) vanishing on them is the zero function *)
Lemma too_many_roots : forall n p rs,
  (length p <= n)%nat -> length rs = n -> NoDup rs ->
  (forall r, In r rs -> Peval p r = 0) -> forall x, Peval p x = 0.
Proof.
  induction n as [|n IH]; intros p rs Hlen Hrs Hnd Hroots x.
  - destruct p; [ reflexivity | cbn [length] in Hlen; lia ].
  - destruct p as [|c p']; [ reflexivity | ].
    destruct rs as [|r0 rs']; [ cbn [length] in Hrs; lia | ].
    assert (Hr0 : Peval (c :: p') r0 = 0) by (apply Hroots; left; reflexivity).
    set (q := removelast (quo r0 (c :: p'))).
    assert (Hqeval : forall y, Peval q y = Peval (quo r0 (c :: p')) y)
      by (intro y; apply Peval_removelast0, last_quo).
    assert (Hfact : forall y, Peval (c :: p') y = (y - r0) * Peval q y).
    { intro y. rewrite Hqeval, (quo_eval r0 (c :: p') y), Hr0; ring. }
    assert (Hqlen : (length q <= n)%nat).
    { unfold q. rewrite length_removelast_cons by (cbn [quo]; discriminate).
      rewrite length_quo. cbn [length] in Hlen |- *. lia. }
    assert (Hqroots : forall r, In r rs' -> Peval q r = 0).
    { intros r Hr. assert (Hrne : r <> r0).
      { intro; subst r; inversion Hnd; contradiction. }
      assert (H0 : Peval (c :: p') r = 0) by (apply Hroots; right; exact Hr).
      rewrite Hfact in H0. apply Rmult_integral in H0.
      destruct H0 as [H0|H0]; [ | exact H0 ]. exfalso; apply Hrne; lra. }
    assert (Hnd' : NoDup rs') by (inversion Hnd; assumption).
    assert (Hqzero : forall y, Peval q y = 0)
      by (apply (IH q rs' Hqlen); [ cbn [length] in Hrs; lia | exact Hnd' | exact Hqroots ]).
    rewrite Hfact, Hqzero; ring.
Qed.

(* continuity of Peval, and function-zero => coeff-zero *)
Lemma Peval_continuity : forall p x0, continuity_pt (Peval p) x0.
Proof.
  induction p as [|c p IH]; intro x0.
  - apply continuity_pt_const; intros a b; reflexivity.
  - replace (Peval (c :: p)) with (plus_fct (fct_cte c) (mult_fct (fun x => x) (Peval p))).
    2:{ apply functional_extensionality; intro y; unfold plus_fct, fct_cte, mult_fct; reflexivity. }
    apply continuity_pt_plus; [ apply continuity_pt_const; intros a b; reflexivity | ].
    apply continuity_pt_mult; [ | apply IH ].
    intros eps Heps; exists eps; split; [ exact Heps | ].
    intros x [_ Hx]; unfold R_dist in *; exact Hx.
Qed.
Lemma f0_of_mult : forall f, continuity_pt f 0 -> (forall x, x <> 0 -> f x = 0) -> f 0 = 0.
Proof.
  intros f Hcont Hz. destruct (Req_dec (f 0) 0) as [|Hne]; [ assumption | exfalso ].
  destruct (Hcont (Rabs (f 0)) (Rabs_pos_lt _ Hne)) as [alp [Halp Hd]].
  specialize (Hd (alp / 2)).
  assert (Hx0 : alp / 2 <> 0) by lra.
  assert (Hcond : D_x no_cond 0 (alp / 2) /\ R_dist (alp / 2) 0 < alp).
  { split; [ split; [ exact I | lra ] | unfold R_dist; rewrite Rminus_0_r, Rabs_right; lra ]. }
  specialize (Hd Hcond).
  assert (Hd' : R_dist (f (alp / 2)) (f 0) < Rabs (f 0)) by exact Hd.
  assert (Hcontra : R_dist (f (alp / 2)) (f 0) = Rabs (f 0)).
  { rewrite (Hz (alp/2) Hx0); unfold R_dist; rewrite Rabs_minus_sym, Rminus_0_r; reflexivity. }
  rewrite Hcontra in Hd'; lra.
Qed.
Lemma poly_fun_zero_coeffs : forall p, (forall x, Peval p x = 0) -> forall i, nth i p 0 = 0.
Proof.
  induction p as [|c p IH]; intros H i; [ destruct i; reflexivity | ].
  assert (Hc : c = 0) by (specialize (H 0); cbn [Peval] in H; lra).
  assert (Hp' : forall x, Peval p x = 0).
  { assert (Hnz : forall x, x <> 0 -> Peval p x = 0).
    { intros x Hx. specialize (H x); cbn [Peval] in H; rewrite Hc in H.
      apply (Rmult_eq_reg_l x); [ rewrite Rmult_0_r; lra | exact Hx ]. }
    intro x; destruct (Req_dec x 0) as [->|Hx]; [ apply f0_of_mult; [ apply Peval_continuity | exact Hnz ] | apply Hnz; exact Hx ]. }
  destruct i as [|i]; cbn [nth]; [ exact Hc | apply IH; exact Hp' ].
Qed.

(* ---- poly from roots: ∏ (X - r_k) ---- *)
Lemma length_Xsub : forall r p, length (Xsub r p) = S (length p).
Proof. intros r p; unfold Xsub; rewrite length_Padd, length_Pscale; cbn [length]; lia. Qed.
Fixpoint PFR (rs : list R) : list R :=
  match rs with [] => [1] | r :: rs' => Xsub r (PFR rs') end.
Lemma PFR_length : forall rs, length (PFR rs) = S (length rs).
Proof. induction rs as [|r rs IH]; cbn [PFR length]; [ reflexivity | rewrite length_Xsub, IH; reflexivity ]. Qed.
Lemma PFR_root : forall rs r, In r rs -> Peval (PFR rs) r = 0.
Proof.
  induction rs as [|r0 rs IH]; intros r Hr; [ inversion Hr | ].
  cbn [PFR]; rewrite Peval_Xsub. destruct Hr as [->|Hr]; [ ring | ].
  rewrite (IH r Hr); ring.
Qed.
Lemma PFR_leading : forall rs, nth (length rs) (PFR rs) 0 = 1.
Proof.
  induction rs as [|r0 rs IH]; [ reflexivity | ].
  cbn [PFR length]; unfold Xsub; rewrite nth_Padd, nth_Pscale.
  cbn [nth]. rewrite IH.
  rewrite (nth_overflow (PFR rs)) by (rewrite PFR_length; lia). ring.
Qed.
Lemma PFR_second : forall rs, rs <> [] -> nth (pred (length rs)) (PFR rs) 0 = - fold_right Rplus 0 rs.
Proof.
  induction rs as [|r0 rs IH]; intro Hne; [ congruence | ].
  destruct rs as [|r1 rs'].
  - cbn [PFR length pred nth Xsub Padd Pscale map fold_right]. ring.
  - change (PFR (r0 :: r1 :: rs')) with (Xsub r0 (PFR (r1 :: rs'))).
    replace (pred (length (r0 :: r1 :: rs'))) with (S (length rs')) by (cbn [length pred]; reflexivity).
    unfold Xsub; rewrite nth_Padd, nth_Pscale.
    change (nth (S (length rs')) (0 :: PFR (r1 :: rs')) 0) with (nth (length rs') (PFR (r1 :: rs')) 0).
    change (S (length rs')) with (length (r1 :: rs')).
    rewrite (PFR_leading (r1 :: rs')).
    replace (length rs') with (pred (length (r1 :: rs'))) by (cbn [length pred]; reflexivity).
    rewrite (IH ltac:(discriminate)).
    cbn [fold_right]. ring.
Qed.

(* ---- Vieta: sum of roots = - a_{m-1}/a_m ---- *)
Theorem vieta_sum : forall (p rs : list R),
  length p = S (length rs) -> rs <> [] -> NoDup rs ->
  (forall r, In r rs -> Peval p r = 0) ->
  nth (length rs) p 0 <> 0 ->
  fold_right Rplus 0 rs = - (nth (pred (length rs)) p 0) / (nth (length rs) p 0).
Proof.
  intros p rs Hlen Hne Hnd Hroots Hlead.
  set (am := nth (length rs) p 0) in *.
  set (D := Padd p (Pscale (-1) (Pscale am (PFR rs)))).
  assert (HDlen : length D = S (length rs)).
  { unfold D; rewrite length_Padd, !length_Pscale, PFR_length, Hlen; lia. }
  assert (HnthD : forall i, nth i D 0 = nth i p 0 - am * nth i (PFR rs) 0).
  { intro i; unfold D; rewrite nth_Padd, nth_Pscale, nth_Pscale; ring. }
  assert (HDlead : nth (length rs) D 0 = 0)
    by (rewrite HnthD, PFR_leading; unfold am; ring).
  assert (HDne : D <> []) by (intro HH; rewrite HH in HDlen; cbn in HDlen; lia).
  assert (HlastD : last D 0 = 0)
    by (rewrite last_nth by exact HDne; rewrite HDlen; cbn [pred]; exact HDlead).
  assert (HDroot : forall r, In r rs -> Peval D r = 0).
  { intros r Hr; unfold D; rewrite Peval_add, Peval_scale, Peval_scale, (PFR_root rs r Hr), (Hroots r Hr); ring. }
  assert (HDzero : forall x, Peval D x = 0).
  { intro x. rewrite <- (Peval_removelast0 D x HlastD).
    apply (too_many_roots (length rs) (removelast D) rs); [ | reflexivity | exact Hnd | ].
    - rewrite length_removelast_cons by exact HDne; rewrite HDlen; cbn [pred]; lia.
    - intros r Hr; rewrite (Peval_removelast0 D r HlastD); apply HDroot; exact Hr. }
  assert (HDcoeff := poly_fun_zero_coeffs D HDzero (pred (length rs))).
  rewrite HnthD, (PFR_second rs Hne) in HDcoeff.
  apply (Rmult_eq_reg_r am); [ | exact Hlead ].
  replace (- nth (pred (length rs)) p 0 / am * am) with (- nth (pred (length rs)) p 0)
    by (field; exact Hlead).
  replace (am * (- fold_right Rplus 0 rs)) with (- (fold_right Rplus 0 rs * am)) in HDcoeff by ring.
  lra.
Qed.


(* ================================================================= *)
(*  Pcot as a coefficient list, and its leading / second coeffs      *)
(* ================================================================= *)
Lemma Peval_coeffs : forall f m x, Peval (map f (seq 0 (S m))) x = sum_f_R0 (fun i => f i * x ^ i) m.
Proof.
  intros f m x; induction m as [|m IH]; [ cbn; ring | ].
  rewrite seq_S, map_app, Peval_app, IH, length_map, length_seq, tech5.
  cbn [Nat.add map Peval]. ring.
Qed.
Lemma sum_f_R0_reverse : forall f n, sum_f_R0 f n = sum_f_R0 (fun i => f (n - i)%nat) n.
Proof.
  intros f n; induction n as [|n IH]; [ reflexivity | ].
  rewrite tech5, IH, (decomp_sum (fun i => f (S n - i)%nat) (S n) ltac:(lia)).
  cbn [pred]. rewrite Nat.sub_0_r.
  replace (sum_f_R0 (fun i => f (S n - S i)%nat) n) with (sum_f_R0 (fun i => f (n - i)%nat) n)
    by (apply sum_eq; intros i Hi; f_equal; lia).
  ring.
Qed.

Definition Plist (m : nat) : list R :=
  map (fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)) (seq 0 (S m)).

Lemma Plist_length : forall m, length (Plist m) = S m.
Proof. intro m; unfold Plist; rewrite length_map, length_seq; reflexivity. Qed.

Lemma Peval_Plist : forall m x, Peval (Plist m) x = Pcot m x.
Proof.
  intros m x; unfold Plist, Pcot.
  rewrite Peval_coeffs.
  rewrite (sum_f_R0_reverse (fun j => (-1)^j * Binomial.C (2*m+1) (2*j+1) * x ^ (m - j))).
  apply sum_eq; intros i Hi.
  replace (m - (m - i))%nat with i by lia. ring.
Qed.

Lemma Plist_leading : forall m, nth m (Plist m) 0 = Binomial.C (2 * m + 1) 1.
Proof.
  intro m; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) m 0 (g 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat m), seq_nth by lia. cbn [Nat.add].
  unfold g. rewrite Nat.sub_diag. cbn [pow]. rewrite Nat.mul_0_r. cbn [Nat.add]. ring.
Qed.

Lemma Plist_second : forall m, (1 <= m)%nat -> nth (pred m) (Plist m) 0 = - Binomial.C (2 * m + 1) 3.
Proof.
  intros m Hm; unfold Plist.
  set (g := fun i => (-1) ^ (m - i) * Binomial.C (2 * m + 1) (2 * (m - i) + 1)).
  rewrite (@nth_indep R (map g (seq 0 (S m))) (pred m) 0 (g 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g (seq 0 (S m)) 0%nat (pred m)), seq_nth by lia. cbn [Nat.add].
  unfold g. replace (m - pred m)%nat with 1%nat by lia. cbn [pow].
  change (2 * 1 + 1)%nat with 3%nat. ring.
Qed.

(* ================================================================= *)
(*  binomial-coefficient arithmetic: C(2m+1,3)/C(2m+1,1) = m(2m-1)/3 *)
(* ================================================================= *)
Lemma fact_plus2 : forall k, fact (k + 2) = ((k + 2) * ((k + 1) * fact k))%nat.
Proof. intro k; replace (k + 2)%nat with (S (S k)) by lia; replace (k + 1)%nat with (S k) by lia; cbn [fact]; ring. Qed.

Lemma C_n_1 : forall n, (1 <= n)%nat -> Binomial.C n 1 = INR n.
Proof.
  intros n Hn; unfold Binomial.C.
  replace (n - 1)%nat with (pred n) by lia.
  assert (Hf : fact n = (n * fact (pred n))%nat) by (destruct n; [ lia | cbn [fact pred]; reflexivity ]).
  rewrite Hf, mult_INR. simpl (fact 1). simpl (INR 1).
  assert (INR (fact (pred n)) <> 0) by apply INR_fact_neq_0.
  field; assumption.
Qed.

Lemma C_ratio : forall m, (1 <= m)%nat ->
  Binomial.C (2 * m + 1) 3 / Binomial.C (2 * m + 1) 1 = INR m * (2 * INR m - 1) / 3.
Proof.
  intros m Hm.
  assert (Hf : fact (2 * m) = ((2 * m) * ((2 * m - 1) * fact (2 * m - 2)))%nat).
  { pose proof (fact_plus2 (2 * m - 2)) as Hp.
    replace (2 * m - 2 + 2)%nat with (2 * m)%nat in Hp by lia.
    replace (2 * m - 2 + 1)%nat with (2 * m - 1)%nat in Hp by lia.
    exact Hp. }
  unfold Binomial.C.
  replace (2 * m + 1 - 1)%nat with (2 * m)%nat by lia.
  replace (2 * m + 1 - 3)%nat with (2 * m - 2)%nat by lia.
  rewrite Hf.
  rewrite !mult_INR, minus_INR by lia.
  simpl (fact 1). simpl (fact 3). simpl (INR 1). simpl (INR 3).
  replace (INR (2 * m)) with (2 * INR m) by (rewrite mult_INR; simpl (INR 2); ring).
  replace (INR 6) with 6 by (simpl; ring). replace (INR 2) with 2 by (simpl; ring).
  assert (H1 : INR (fact (2 * m + 1)) <> 0) by apply INR_fact_neq_0.
  assert (H2 : INR (fact (2 * m - 2)) <> 0) by apply INR_fact_neq_0.
  assert (Hmpos : 0 < INR m) by (apply lt_0_INR; lia).
  assert (Hm1 : 1 <= INR m) by (replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia).
  assert (H3 : 2 * INR m - 1 <> 0) by (apply Rgt_not_eq; lra).
  field. repeat split; try assumption; lra.
Qed.

(* ================================================================= *)
(*  the roots r_k = cot²(kπ/(2m+1)), k=1..m                           *)
(* ================================================================= *)
Definition theta (m k : nat) : R := INR k * PI / INR (2 * m + 1).

Lemma den_pos : forall m, 0 < INR (2 * m + 1).
Proof. intro m; apply lt_0_INR; lia. Qed.

Lemma theta_pos : forall m k, (1 <= k)%nat -> 0 < theta m k.
Proof.
  intros m k Hk; unfold theta; apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat; [ apply lt_0_INR; lia | apply PI_RGT_0 ].
  - apply den_pos.
Qed.

Lemma theta_lt : forall m k, (k <= m)%nat -> theta m k < PI / 2.
Proof.
  intros m k Hk; unfold theta.
  apply Rmult_lt_reg_r with (r := INR (2 * m + 1)); [ apply den_pos | ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rgt_not_eq, den_pos).
  replace (INR (2 * m + 1)) with (2 * INR m + 1)
    by (rewrite plus_INR, mult_INR; simpl (INR 2); simpl (INR 1); ring).
  assert (INR k <= INR m) by (apply le_INR; exact Hk).
  pose proof PI_RGT_0. nra.
Qed.

Lemma sin_theta_pos : forall m k, (1 <= k)%nat -> (k <= m)%nat -> 0 < sin (theta m k).
Proof.
  intros m k Hk1 Hkm; apply sin_gt_0; [ apply theta_pos; exact Hk1 | ].
  apply Rlt_trans with (PI / 2); [ apply theta_lt; exact Hkm | ].
  pose proof PI_RGT_0; lra.
Qed.

Lemma root_of : forall m k, (1 <= k)%nat -> (k <= m)%nat ->
  Pcot m (Rcot (theta m k) ^ 2) = 0.
Proof.
  intros m k Hk1 Hkm.
  assert (Hsin : sin (theta m k) <> 0) by (apply Rgt_not_eq, sin_theta_pos; assumption).
  pose proof (sin_eq_sinpow_Pcot m (theta m k) Hsin) as HE.
  assert (Hzero : sin (INR (2 * m + 1) * theta m k) = 0).
  { replace (INR (2 * m + 1) * theta m k) with (INR k * PI)
      by (unfold theta; field; apply Rgt_not_eq, den_pos).
    apply sin_eq_0_1; exists (Z.of_nat k); rewrite INR_IZR_INZ; reflexivity. }
  rewrite Hzero in HE; symmetry in HE; apply Rmult_integral in HE.
  destruct HE as [HE|HE]; [ exfalso; apply (pow_nonzero (sin (theta m k)) (2 * m + 1) Hsin); exact HE | exact HE ].
Qed.

(* strict monotonicity of cot on (0,π/2) *)
Lemma Rcot_pos : forall x, 0 < x -> x < PI / 2 -> 0 < Rcot x.
Proof.
  intros x H1 H2; pose proof PI_RGT_0; unfold Rcot.
  apply Rdiv_lt_0_compat; [ apply cos_gt_0; lra | apply sin_gt_0; lra ].
Qed.
Lemma Rcot_decr : forall a b, 0 < a -> a < b -> b < PI / 2 -> Rcot b < Rcot a.
Proof.
  intros a b Ha Hab Hb; pose proof PI_RGT_0.
  assert (Hsa : 0 < sin a) by (apply sin_gt_0; lra).
  assert (Hca : 0 < cos a) by (apply cos_gt_0; lra).
  assert (Hsb : 0 < sin b) by (apply sin_gt_0; lra).
  assert (Hcb : 0 < cos b) by (apply cos_gt_0; lra).
  assert (Hta : Rcot a = / tan a) by (unfold Rcot, tan; field; lra).
  assert (Htb : Rcot b = / tan b) by (unfold Rcot, tan; field; lra).
  assert (Htap : 0 < tan a) by (apply tan_gt_0; lra).
  assert (Htbp : 0 < tan b) by (apply tan_gt_0; lra).
  assert (Htab : tan a < tan b) by (apply tan_increasing; lra).
  rewrite Hta, Htb; apply Rinv_lt_contravar; [ apply Rmult_lt_0_compat; assumption | exact Htab ].
Qed.

(* distinctness of the r_k *)
Lemma theta_mono : forall m a b, (a < b)%nat -> theta m a < theta m b.
Proof.
  intros m a b Hab; unfold theta; apply Rmult_lt_compat_r.
  - apply Rinv_0_lt_compat, den_pos.
  - apply Rmult_lt_compat_r; [ apply PI_RGT_0 | apply lt_INR; exact Hab ].
Qed.
Lemma rsq_inj : forall m a b, (1 <= a)%nat -> (a <= m)%nat -> (1 <= b)%nat -> (b <= m)%nat ->
  Rcot (theta m a) ^ 2 = Rcot (theta m b) ^ 2 -> a = b.
Proof.
  intros m a b Ha1 Ham Hb1 Hbm Heq.
  destruct (Nat.lt_trichotomy a b) as [Hlt|[Heq'|Hgt]]; [ | exact Heq' | ]; exfalso.
  - assert (Ht : theta m a < theta m b) by (apply theta_mono; exact Hlt).
    assert (Rcot (theta m b) < Rcot (theta m a))
      by (apply Rcot_decr; [ apply theta_pos; exact Ha1 | exact Ht | apply theta_lt; exact Hbm ]).
    assert (0 < Rcot (theta m b)) by (apply Rcot_pos; [ apply theta_pos; exact Hb1 | apply theta_lt; exact Hbm ]).
    nra.
  - assert (Ht : theta m b < theta m a) by (apply theta_mono; exact Hgt).
    assert (Rcot (theta m a) < Rcot (theta m b))
      by (apply Rcot_decr; [ apply theta_pos; exact Hb1 | exact Ht | apply theta_lt; exact Ham ]).
    assert (0 < Rcot (theta m a)) by (apply Rcot_pos; [ apply theta_pos; exact Ha1 | apply theta_lt; exact Ham ]).
    nra.
Qed.

Lemma NoDup_map_inj : forall (f : nat -> R) (l : list nat),
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros f l; induction l as [|x l IH]; intros Hinj Hnd; cbn [map]; [ constructor | ].
  inversion Hnd as [| ? ? Hnx Hnd']; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hiny]].
    apply Hnx. replace x with y; [ exact Hiny | apply Hinj; [ right; exact Hiny | left; reflexivity | exact Hy ] ].
  - apply IH; [ intros a b Ha Hb; apply Hinj; right; assumption | exact Hnd' ].
Qed.

(* ================================================================= *)
(*  the main theorem: Σ_{k=1}^m cot²(kπ/(2m+1)) = m(2m-1)/3           *)
(* ================================================================= *)
Lemma fold_right_app_single : forall (l : list R) x, fold_right Rplus 0 (l ++ [x]) = fold_right Rplus 0 l + x.
Proof. induction l as [|c l IH]; intro x; cbn [app fold_right]; [ ring | rewrite IH; ring ]. Qed.

Lemma fold_right_map_seq : forall (g : nat -> R) m, (1 <= m)%nat ->
  fold_right Rplus 0 (map g (seq 1 m)) = sum_f_R0 (fun k => g (S k)) (m - 1).
Proof.
  intros g m Hm; induction m as [|m IH]; [ lia | ].
  destruct (Nat.eq_dec m 0) as [->|Hm0]; [ cbn; ring | ].
  rewrite seq_S, map_app. cbn [map]. rewrite fold_right_app_single, (IH ltac:(lia)).
  replace (S m - 1)%nat with (S (m - 1)) by lia. rewrite tech5.
  replace (S (m - 1)) with m by lia. replace (1 + m)%nat with (S m) by lia. reflexivity.
Qed.

Theorem cot_sq_sum : forall m, (1 <= m)%nat ->
  sum_f_R0 (fun k => Rcot (INR (S k) * PI / INR (2 * m + 1)) ^ 2) (m - 1)
  = INR m * (2 * INR m - 1) / 3.
Proof.
  intros m Hm.
  set (rs := map (fun k => Rcot (theta m k) ^ 2) (seq 1 m)).
  assert (Hlen_rs : length rs = m) by (unfold rs; rewrite length_map, length_seq; reflexivity).
  assert (Hnd : NoDup rs).
  { unfold rs; apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros a b Ha Hb Heq; apply in_seq in Ha; apply in_seq in Hb; apply (rsq_inj m a b); [ lia | lia | lia | lia | exact Heq ]. }
  assert (Hne : rs <> []).
  { unfold rs; intro HH; apply (f_equal (@length R)) in HH; rewrite length_map, length_seq in HH; cbn in HH; lia. }
  assert (Hroots : forall r, In r rs -> Peval (Plist m) r = 0).
  { intros r Hr; unfold rs in Hr; apply in_map_iff in Hr; destruct Hr as [k [Hk Hink]].
    apply in_seq in Hink; subst r; rewrite Peval_Plist; apply root_of; lia. }
  assert (Hlead : nth (length rs) (Plist m) 0 <> 0)
    by (rewrite Hlen_rs, Plist_leading, C_n_1 by lia; apply not_0_INR; lia).
  assert (Hpl : length (Plist m) = S (length rs)) by (rewrite Plist_length, Hlen_rs; reflexivity).
  pose proof (vieta_sum (Plist m) rs Hpl Hne Hnd Hroots Hlead) as HV.
  rewrite Hlen_rs, (Plist_second m Hm), (Plist_leading m) in HV.
  unfold rs in HV; rewrite (fold_right_map_seq (fun k => Rcot (theta m k) ^ 2) m Hm) in HV.
  unfold theta in HV.
  rewrite HV, <- (C_ratio m Hm), Ropp_involutive. reflexivity.
Qed.

Print Assumptions cot_sq_sum.

(* ================================================================= *)
(*  END BaselVieta.v.  Σ cot²(kπ/(2m+1)) = m(2m-1)/3, via Vieta.      *)
(* ================================================================= *)
