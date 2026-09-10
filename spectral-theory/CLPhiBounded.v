(* ================================================================= *)
(*  CLPhiBounded.v  --  Phi(sigma,chi) stays BOUNDED as sigma -> 1+   *)
(*  for every non-principal chi.                                      *)
(*                                                                    *)
(*  This is the half of Dirichlet's theorem that does NOT diverge.     *)
(*  Paired with CLPrincipalLogDeriv (where chi_0 does diverge) and     *)
(*  CharSelectorSeries (which combines them), it is what forces the    *)
(*  residue class to be infinite.                                     *)
(*                                                                    *)
(*  THE ROUTE AVOIDS L' ENTIRELY.  The textbook argument bounds        *)
(*  Phi = -L'/L by showing L' is continuous at s = 1, which needs      *)
(*  "the derivative of a holomorphic function is holomorphic"          *)
(*  (CDerivHoloDisk.holo_deriv_fun) plus a clamp adapter to move a     *)
(*  half-plane function onto a disk centred at 0.  None of that is     *)
(*  needed: CVonMangoldtLChi.phi_L_eq already gives Phi * L = D with   *)
(*  D(s) = sum chi(n) ln n n^{-s}, and D is bounded DIRECTLY by Abel   *)
(*  summation -- CAbelTail.Cabel_tail against CCharSumBound.PS_bound,  *)
(*  with the weight decreasing from n = 3 on (CLWeightAnti.wln_anti).  *)
(*  Then Phi = D / L, and L only has to be bounded BELOW, which is     *)
(*  continuity of L (is_Cderiv_cont, cheap) plus L(1,chi) <> 0.        *)
(*                                                                    *)
(*  Restricting to REAL sigma is what makes the weight real and hence  *)
(*  monotone; sigma -> 1+ along the reals is all the theorem needs.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus Holomorphic CHoloCalculus CexpFull
        CSeries CListSum CDirichlet GaussSum CCharSumBound CharModulus
        RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff CLSeries
        CLHolo1 CLHolo3 LFunOne CVonMangoldtChi CVonMangoldtLChi
        CAbelTail CLWeightAnti CEulerProductZeta CLLogDeriv CZetaTerm2.
Import ListNotations.
Open Scope R_scope.

Lemma Cmod_split2 : forall x y : C, Cmod x <= Cmod (Cminus x y) + Cmod y.
Proof.
  intros x y. replace (Cmod x) with (Cmod (Cadd (Cminus x y) y)) by (f_equal; ring).
  apply Cmod_triangle.
Qed.

Lemma Cmod_minus_comm : forall x y : C, Cmod (Cminus x y) = Cmod (Cminus y x).
Proof.
  intros x y. replace (Cminus x y) with (Copp (Cminus y x)) by ring.
  apply Cmod_opp.
Qed.

Section PhiB.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.

Definition sc (sig : R) : C := mkC sig 0.

Definition dtm (sig : R) (k : nat) : C :=
  Cmul (dchar p g A (S k)) (RtoC (wln sig k)).

Definition Kb : R := ln 2 / 2 + ln 3 / 3 + 2 * INR p * (ln 4 / 4).

(* ---- the ln-weighted term is a character times a real weight ---- *)

Lemma dtm_eq : forall sig k,
  Cmul (RtoC (ln (INR (S k)))) (Lterm p g A (sc sig) k) = dtm sig k.
Proof.
  intros sig k. unfold Lterm, Gchi, dtm, wln.
  replace (Copp (sc sig)) with (RtoC (- sig))
    by (apply Ceq; unfold Copp, RtoC, sc; cbn [Re Im]; ring).
  rewrite Cpw_RtoC.
  apply Ceq; unfold Cmul, RtoC; cbn [Re Im]; ring.
Qed.

Lemma PSbnd : forall n, Cmod (Cpsum (fun k => dchar p g A (S k)) n) <= INR p.
Proof.
  intro n.
  replace (Cpsum (fun k => dchar p g A (S k)) n) with (PS p g A (S n)).
  - apply (PS_bound p g A Hp Hg Hord HA).
  - unfold PS, Sf.
    change (fold_right Cadd C0 (map (dchar p g A) (seq 1 (S n))))
      with (Cls (seq 1 (S n)) (dchar p g A)).
    symmetry. apply Cpsum_shift_eq_Cls.
Qed.

Lemma Cmod_dtm : forall sig k, Cmod (dtm sig k) <= wln sig k.
Proof.
  intros sig k. unfold dtm.
  rewrite Cmod_mul_RtoC, (Rabs_pos_eq _ (wln_nonneg sig k)).
  pose proof (Cmod_dchar_le p g A (S k)) as H.
  pose proof (wln_nonneg sig k). nra.
Qed.

(* ---- the first three terms ---- *)

Lemma wln_0 : forall sig, wln sig 0%nat = 0.
Proof.
  intro sig. unfold wln. replace (INR 1) with 1 by (simpl; ring).
  rewrite ln_1. ring.
Qed.

Lemma wln_small : forall sig, 1 <= sig ->
  wln sig 1%nat <= ln 2 / 2 /\ wln sig 2%nat <= ln 3 / 3
  /\ wln sig 3%nat <= ln 4 / 4.
Proof.
  intros sig Hs.
  pose proof (wln_le sig 1%nat Hs) as H1.
  pose proof (wln_le sig 2%nat Hs) as H2.
  pose proof (wln_le sig 3%nat Hs) as H3.
  replace (INR 2) with 2 in H1 by (simpl; ring).
  replace (INR 3) with 3 in H2 by (simpl; ring).
  replace (INR 4) with 4 in H3 by (simpl; ring).
  auto.
Qed.

Lemma head_bound : forall sig, 1 <= sig ->
  Cmod (Cpsum (dtm sig) 2) <= ln 2 / 2 + ln 3 / 3.
Proof.
  intros sig Hs.
  destruct (wln_small sig Hs) as [H1 [H2 _]].
  eapply Rle_trans; [ apply Cmod_Cpsum_le | ].
  replace (sum_f_R0 (fun k => Cmod (dtm sig k)) 2)
    with (Cmod (dtm sig 0%nat) + Cmod (dtm sig 1%nat) + Cmod (dtm sig 2%nat))
    by reflexivity.
  pose proof (Cmod_dtm sig 0%nat) as C0'.
  pose proof (Cmod_dtm sig 1%nat) as C1'.
  pose proof (Cmod_dtm sig 2%nat) as C2'.
  rewrite (wln_0 sig) in C0'.
  pose proof (Cmod_nonneg (dtm sig 0%nat)). lra.
Qed.

(* ---- the uniform bound on every partial sum ---- *)

Theorem dtm_partial_bound : forall sig N, 1 <= sig ->
  Cmod (Cpsum (dtm sig) N) <= Kb.
Proof.
  intros sig N Hs.
  destruct (wln_small sig Hs) as [_ [_ H3]].
  pose proof (head_bound sig Hs) as Hh.
  assert (Hp0 : 0 <= INR p) by apply pos_INR.
  assert (Hln4 : 0 <= ln 4 / 4)
    by (unfold Rdiv; apply Rmult_le_pos;
        [ rewrite <- ln_1; apply ln_le'; lra | lra ]).
  destruct (le_lt_dec N 2) as [Hle | Hgt].
  - (* short sums: bound the at most three terms directly *)
    assert (Hsub : Cmod (Cpsum (dtm sig) N) <= ln 2 / 2 + ln 3 / 3).
    { destruct (wln_small sig Hs) as [H1 [H2 _]].
      pose proof (Cmod_dtm sig 0%nat) as C0'. rewrite (wln_0 sig) in C0'.
      pose proof (Cmod_dtm sig 1%nat) as C1'.
      pose proof (Cmod_dtm sig 2%nat) as C2'.
      pose proof (Cmod_nonneg (dtm sig 0%nat)).
      pose proof (Cmod_nonneg (dtm sig 1%nat)).
      pose proof (Cmod_nonneg (dtm sig 2%nat)).
      destruct N as [| [| [| N']]]; [ | | | lia ];
        (eapply Rle_trans; [ apply Cmod_Cpsum_le | ]);
        cbn [sum_f_R0]; lra. }
    unfold Kb. nra.
  - (* long sums: Abel from n = 3 on *)
    assert (Hj : N = (2 + S (N - 3))%nat) by lia.
    assert (Htail : Cmod (Cminus (Cpsum (dtm sig) N) (Cpsum (dtm sig) 2))
                    <= 2 * INR p * wln sig 3).
    { rewrite Hj at 1.
      apply (Cabel_tail (fun k => dchar p g A (S k)) (wln sig) (INR p) 2 (N - 3)).
      - apply PSbnd.
      - intros n Hn. apply wln_anti; [ exact Hs | lia ]. }
    assert (Htri : Cmod (Cpsum (dtm sig) N)
                   <= Cmod (Cminus (Cpsum (dtm sig) N) (Cpsum (dtm sig) 2))
                      + Cmod (Cpsum (dtm sig) 2)).
    { apply Cmod_split2. }
    unfold Kb. nra.
Qed.

(* ---- hence the limit is bounded ---- *)

Theorem Phi_L_mod_bound : forall sig (Hs : 1 < Re (sc sig)),
  Cmod (Cmul (Phichi p g A Hg Hord (sc sig) Hs)
             (LFun p g A Hp Hg Hord HA (sc sig))) <= Kb.
Proof.
  intros sig Hs.
  assert (Hs1 : 1 <= sig) by (cbn in Hs; lra).
  assert (Hs0 : 0 < Re (sc sig)) by (cbn in Hs |- *; lra).
  pose proof (phi_L_eq p g A Hp Hg Hord (sc sig) Hs
                (LFun p g A Hp Hg Hord HA (sc sig))
                (LFun_series p g A Hp Hg Hord HA (sc sig) Hs0)) as Hcv.
  assert (Hcp : CUn_cv (Cpsum (dtm sig))
                  (Cmul (Phichi p g A Hg Hord (sc sig) Hs)
                        (LFun p g A Hp Hg Hord HA (sc sig)))).
  { apply (CUn_cv_ext (fun N => Cls (seq 1 (S N))
             (fun n => Cmul (RtoC (ln (INR n))) (Gchi p g A (sc sig) n)))).
    - intro N. rewrite <- Cpsum_shift_eq_Cls.
      apply Cpsum_ext. intro k. apply dtm_eq.
    - apply (CUn_cv_shift (fun N => Cls (seq 1 N)
               (fun n => Cmul (RtoC (ln (INR n))) (Gchi p g A (sc sig) n)))).
      exact Hcv. }
  apply Rle_cv_lim with (Un := fun N => Cmod (Cpsum (dtm sig) N))
                        (Vn := fun _ : nat => Kb).
  - intro N. apply dtm_partial_bound. exact Hs1.
  - apply CUn_cv_Cmod. exact Hcp.
  - intros e He. exists 0%nat. intros n _. unfold R_dist.
    replace (Kb - Kb) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

(* ---- L is bounded below near s = 1 ---- *)

Theorem L_lower : exists c del, 0 < c /\ 0 < del /\
  forall sig, Rabs (sig - 1) < del ->
    c <= Cmod (LFun p g A Hp Hg Hord HA (sc sig)).
Proof.
  set (L1 := LFun p g A Hp Hg Hord HA (mkC 1 0)).
  assert (Hne : L1 <> C0) by (apply (LFun_one_nonzero_all p g A Hp Hg Hord HA)).
  assert (Hc0 : 0 < Cmod L1).
  { destruct (Rle_lt_dec (Cmod L1) 0) as [Hle | Hlt].
    - exfalso. apply Hne. apply (proj1 (Cmod0 L1)).
      pose proof (Cmod_nonneg L1). lra.
    - exact Hlt. }
  assert (H1 : 0 < Re (mkC 1 0)) by (cbn; lra).
  destruct (LFun_holo p g A Hp Hg Hord HA (mkC 1 0) H1) as [d Hd].
  destruct (is_Cderiv_cont _ _ _ Hd (Cmod L1 / 2) ltac:(lra)) as [del [Hdel Hcont]].
  exists (Cmod L1 / 2), del. split; [ lra | split; [ exact Hdel | ] ].
  intros sig Hsig.
  set (h := mkC (sig - 1) 0).
  assert (Hmh : Cmod h = Rabs (sig - 1))
    by (unfold h; replace (mkC (sig - 1) 0) with (RtoC (sig - 1)) by reflexivity;
        apply Cmod_RtoC).
  assert (Hadd : Cadd (mkC 1 0) h = sc sig)
    by (unfold h, sc; apply Ceq; unfold Cadd; cbn [Re Im]; ring).
  pose proof (Hcont h ltac:(lra)) as Hlt.
  rewrite Hadd in Hlt. fold L1 in Hlt.
  assert (Htri : Cmod L1 <= Cmod (Cminus L1 (LFun p g A Hp Hg Hord HA (sc sig)))
                            + Cmod (LFun p g A Hp Hg Hord HA (sc sig)))
    by apply Cmod_split2.
  rewrite Cmod_minus_comm in Htri.
  lra.
Qed.

(* ---- THE bound ---- *)

Theorem Phi_bounded : exists K del, 0 < del /\
  forall sig (Hs : 1 < Re (sc sig)), sig < 1 + del ->
    Cmod (Phichi p g A Hg Hord (sc sig) Hs) <= K.
Proof.
  destruct L_lower as [c [del [Hc [Hdel HL]]]].
  exists (Kb / c), del. split; [ exact Hdel | ].
  intros sig Hs Hlt.
  assert (Hs1 : 1 < sig) by (cbn in Hs; lra).
  assert (Habs : Rabs (sig - 1) < del)
    by (rewrite Rabs_pos_eq by lra; lra).
  pose proof (HL sig Habs) as HLc.
  pose proof (Phi_L_mod_bound sig Hs) as Hb.
  rewrite Cmod_mul in Hb.
  apply (Rmult_le_reg_r c); [ exact Hc | ].
  apply Rle_trans with (Cmod (Phichi p g A Hg Hord (sc sig) Hs)
                        * Cmod (LFun p g A Hp Hg Hord HA (sc sig))).
  - apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact HLc ].
  - apply Rle_trans with Kb; [ exact Hb | ].
    apply Req_le. field. lra.
Qed.

End PhiB.

Print Assumptions Phi_bounded.

(* ================================================================= *)
(*  END CLPhiBounded.v                                                *)
(* ================================================================= *)
