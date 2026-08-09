(* ================================================================= *)
(*  SelbergStarSigned.v  —  the SIGNED log² Selberg identity.           *)
(*                                                                    *)
(*  Iterating the SIGNED degree-1 symmetry (selberg_average_signed,     *)
(*  an equality-with-error, unlike the one-sided unsigned selberg_      *)
(*  average) and reindexing (selberg2_reindex, function-parametric)     *)
(*  gives                                                              *)
(*                                                                    *)
(*    | Vsig(N)·ln²N − Σ Λ2(n)/n·Vsig(N/n) + 2·Σ Λ(n)ln n/n·Vsig(N/n) |  *)
(*        ≤ O(ln N).                                                    *)
(*                                                                    *)
(*  NOTE the 2·Σ Λ·log term: in the unsigned star_inequality it cancels *)
(*  (the log-gap −Dlog matches the reindex −Dlog under the ONE-SIDED    *)
(*  bound); with signs the iterate flips D's sign, so it survives.  So  *)
(*  the signed degree-2 weight is Λ2 − 2Λ·log = Λ∗Λ − Λ·log, NOT pure   *)
(*  Λ2 — the genuine subtlety of Selberg's argument.  Axiom-clean.      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius MobiusOverD
        SelbergEndgame SelbergAverage SelbergAverageSigned SelbergSignedExtremes
        MertensVonMangoldt SelbergSymmetry SelbergIterate StarInequality SelbergSignedConc.
Import ListNotations.
Open Scope R_scope.

Theorem star_signed : forall N, (1 <= N)%nat ->
  Rabs (Vsig N * (ln (INR N) * ln (INR N))
        - Rls (seq 1 N) (fun n => Lam2 n / INR n * Vsig (N / n)%nat)
        + 2 * Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n * Vsig (N / n)%nat))
  <= (Cs + (Kup - 1) * ln 2) * msum N + Cs * ln (INR N).
Proof.
  intros N HN.
  assert (Hl2p : 0 <= ln 2) by (rewrite <- ln_1; left; apply ln_increasing; lra).
  assert (HK1 : 0 <= Kup - 1) by (unfold Kup; pose proof ln2_pos; lra).
  assert (Hln0 : 0 <= ln (INR N))
    by (rewrite <- ln_1; apply ln_le; [ lra | replace 1 with (INR 1) by (simpl; ring); apply le_INR; lia ]).
  set (S1 := Rls (seq 1 N) (fun d => Lam d / INR d * Vsig (N / d)%nat)).
  set (D2 := Rls (seq 1 N) (fun n => Lam2 n / INR n * Vsig (N / n)%nat)).
  set (Dlog := Rls (seq 1 N) (fun n => Lam n * ln (INR n) / INR n * Vsig (N / n)%nat)).
  set (E1 := Rls (seq 1 N) (fun d => Lam d / INR d * Vsig (N / d)%nat *
              (ln (INR (N / d)%nat) - (ln (INR N) - ln (INR d))))).
  set (A := Rls (seq 1 N) (fun d => Lam d / INR d * (Vsig (N / d)%nat * ln (INR (N / d)%nat)))).
  (* log-gap expansion:  A = ln N·S1 − Dlog + E1 *)
  assert (HLGT : A = ln (INR N) * S1 - Dlog + E1).
  { unfold A, S1, Dlog, E1; rewrite Rls_scal, <- Rls_minus', <- Rls_add.
    apply Rls_ext; intros d Hd; apply in_seq in Hd; field; apply not_0_INR; lia. }
  (* |E1| ≤ (Kup−1)·ln2·msum N *)
  assert (HE1 : Rabs E1 <= (Kup - 1) * ln 2 * msum N).
  { unfold E1; eapply Rle_trans; [ apply Rls_abs | ].
    eapply Rle_trans; [ apply Rls_le with (g := fun d => Lam d / INR d * ((Kup - 1) * ln 2)) | ].
    - intros d Hd; apply in_seq in Hd.
      assert (Hq1 : (1 <= N / d)%nat)
        by (pose proof (Nat.Div0.div_mod N d); pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia).
      assert (Hdd : 0 <= Lam d / INR d)
        by (apply Rmult_le_pos; [ apply Lam_nonneg | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ]).
      pose proof (Vrem_bound (N / d)%nat Hq1) as HVb; rewrite Vrem_eq_absVsig in HVb.
      pose proof (log_floor_diff N d ltac:(lia) ltac:(lia)) as Hgap.
      pose proof (Rabs_pos (ln (INR (N / d)%nat) - (ln (INR N) - ln (INR d)))) as Hgp.
      rewrite Rabs_mult, Rabs_mult, (Rabs_right (Lam d / INR d)) by (apply Rle_ge; exact Hdd).
      assert (Hvg : Rabs (Vsig (N / d)%nat) * Rabs (ln (INR (N / d)%nat) - (ln (INR N) - ln (INR d)))
                    <= (Kup - 1) * ln 2) by nra.
      replace (Lam d / INR d * Rabs (Vsig (N / d)%nat) *
                 Rabs (ln (INR (N / d)%nat) - (ln (INR N) - ln (INR d))))
        with (Lam d / INR d * (Rabs (Vsig (N / d)%nat) *
                 Rabs (ln (INR (N / d)%nat) - (ln (INR N) - ln (INR d))))) by ring.
      apply Rmult_le_compat_l; [ exact Hdd | exact Hvg ].
    - rewrite Rls_scal_r, <- msum_Rls; apply Req_le; ring. }
  (* iterate bound:  |A + Dconv| ≤ Cs·msum,  Dconv = D2 − Dlog *)
  assert (HDconv : Rls (seq 1 N) (fun n => Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat)
                                            / INR n * Vsig (N / n)%nat)
                   = D2 - Dlog).
  { unfold D2, Dlog; rewrite <- Rls_minus'; apply Rls_ext; intros n Hn; apply in_seq in Hn.
    assert (Hconv : Rls (divisors n) (fun d => Lam d * Lam (n / d)%nat) = Lam2 n - Lam n * ln (INR n))
      by (unfold Lam2; ring).
    rewrite Hconv; field; apply not_0_INR; lia. }
  assert (Hiter : Rabs (A + (D2 - Dlog)) <= Cs * msum N).
  { unfold A; rewrite <- HDconv, <- (selberg2_reindex N Vsig), <- Rls_add.
    eapply Rle_trans; [ apply Rls_abs | ].
    eapply Rle_trans; [ apply Rls_le with (g := fun d => Lam d / INR d * Cs) | ].
    - intros d Hd; apply in_seq in Hd.
      assert (Hq1 : (1 <= N / d)%nat)
        by (pose proof (Nat.Div0.div_mod N d); pose proof (Nat.mod_upper_bound N d ltac:(lia)); nia).
      assert (Hdd : 0 <= Lam d / INR d)
        by (apply Rmult_le_pos; [ apply Lam_nonneg | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ]).
      replace (Lam d / INR d * (Vsig (N / d)%nat * ln (INR (N / d)%nat)) +
               Lam d / INR d * Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vsig (N / (d * e))%nat))
        with (Lam d / INR d * (Vsig (N / d)%nat * ln (INR (N / d)%nat) +
               Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vsig (N / (d * e))%nat))) by ring.
      rewrite Rabs_mult, (Rabs_right (Lam d / INR d)) by (apply Rle_ge; exact Hdd).
      apply Rmult_le_compat_l; [ exact Hdd | ].
      replace (Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vsig (N / (d * e))%nat))
        with (Rls (seq 1 (N / d)%nat) (fun e => Lam e / INR e * Vsig ((N / d) / e)%nat)).
      2:{ apply Rls_ext; intros e He; apply in_seq in He; rewrite Nat.div_div by lia; reflexivity. }
      unfold Cs; apply (selberg_average_signed (N / d)%nat Hq1).
    - rewrite Rls_scal_r, <- msum_Rls; apply Req_le; ring. }
  (* selberg_average_signed at N, scaled by ln N *)
  pose proof (selberg_average_signed N HN) as Hsel; fold S1 in Hsel.
  assert (Hsel2 : Rabs (Vsig N * (ln (INR N) * ln (INR N)) + ln (INR N) * S1) <= Cs * ln (INR N)).
  { replace (Vsig N * (ln (INR N) * ln (INR N)) + ln (INR N) * S1)
      with (ln (INR N) * (Vsig N * ln (INR N) + S1)) by ring.
    rewrite Rabs_mult, (Rabs_right (ln (INR N))) by (apply Rle_ge; exact Hln0).
    rewrite (Rmult_comm Cs (ln (INR N))).
    apply Rmult_le_compat_l; [ exact Hln0 | unfold Cs; exact Hsel ]. }
  (* combine (all linear in the product-atoms) *)
  apply Rabs_le_inv in HE1, Hiter, Hsel2.
  rewrite HLGT in Hiter.
  apply Rabs_le; lra.
Qed.

Print Assumptions star_signed.

(* ================================================================= *)
(*  END SelbergStarSigned.v  —  the signed log² Selberg identity, with   *)
(*  the surviving 2·Λ·log term (the Selberg subtlety).                  *)
(* ================================================================= *)
