(* ================================================================= *)
(*  CEulerProductConv.v  —  the finite complex Euler product converges  *)
(*  to zetaC on Re s > 1.                                              *)
(*                                                                    *)
(*  cEF s N := ∏_{p ≤ S N} (Σ_{k≤N} (p^{-s})^k)  (truncated product).   *)
(*  Via CEulerFactorSmooth.Ceuler_reindex_fin it is the sum of m^{-s}   *)
(*  over the {p≤S N}-smooth numbers m = code ps ks.  Those smooth       *)
(*  numbers include every n ∈ [1..S N] (factorization existence), so    *)
(*  the difference cEF s N − Σ_{n≤S N} n^{-s} is a sum over the EXTRA    *)
(*  smooth numbers, all > S N, whose modulus is bounded by the real     *)
(*  tail zeta_cont σ − Σ_{n≤S N} n^{-σ} → 0 (σ = Re s), reusing         *)
(*  recip_s_nodup_bound and operator_zeta_eq_cont.  With the Dirichlet  *)
(*  partial sums → zetaC s (CDirichlet.zetaC_eq_dirichlet), a squeeze    *)
(*  gives cEF s N → zetaC s.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List QArith Arith.
Require Import ComplexField Cmodulus CexpFull CPowMul RootsOfUnity DirichletLEuler
        CSeries CZetaTerm CZeta CDirichlet CEulerFactorSmooth
        PrimonGas PrimeFactorizationN PrimeFactorizationExists EulerReindex
        EulerProductZeta EulerProductZetaBound RecipSquareBound EulerProductZetaCont
        Ell2Zeta Ell2ZetaConverge Ell2ZetaCont ZetaContinuation.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  0.  complex finite-sum modulus helpers                           *)
(* ================================================================= *)

Lemma Cmod_C0 : Cmod C0 = 0.
Proof. apply (proj2 (Cmod0 C0)); reflexivity. Qed.

Lemma Cwsum_cons : forall x l, Cwsum (x :: l) = Cadd x (Cwsum l).
Proof. intros x l; unfold Cwsum; reflexivity. Qed.

Lemma Cmod_Cwsum_le : forall l, Cmod (Cwsum l) <= Rlsum (map Cmod l).
Proof.
  intro l; induction l as [|a l IH]; cbn [map].
  - unfold Cwsum, Rlsum; cbn [fold_right]; rewrite Cmod_C0; apply Rle_refl.
  - rewrite Cwsum_cons, Rlsum_cons.
    eapply Rle_trans; [ apply Cmod_triangle | apply Rplus_le_compat_l; exact IH ].
Qed.

(* complex analogue of RecipSquareBound.sum_remove *)
Lemma Cwsum_remove : forall (g : nat -> C) r l, In r l -> NoDup l ->
  Cwsum (map g l) = Cadd (g r) (Cwsum (map g (remove Nat.eq_dec r l))).
Proof.
  intros g r l; induction l as [|a l IH]; intros Hin Hnd; [ destruct Hin | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  cbn [map remove]; rewrite Cwsum_cons.
  destruct (Nat.eq_dec r a) as [He | Hne].
  - subst a; rewrite (notin_remove Nat.eq_dec l r Hnin); reflexivity.
  - destruct Hin as [Ha | Hin]; [ symmetry in Ha; contradiction | ].
    cbn [map]; rewrite Cwsum_cons, (IH Hin Hnd'); ring.
Qed.

(* the key bound: over a NoDup superset, the modulus of the missing part *)
(* is at most the real gap of the moduli (mirror of incl_sum_le)         *)
Lemma Cmod_Cwsum_incl_diff : forall (g : nat -> C) L S,
  NoDup L -> NoDup S -> incl S L ->
  Cmod (Cminus (Cwsum (map g L)) (Cwsum (map g S)))
  <= Rlsum (map (fun m => Cmod (g m)) L) - Rlsum (map (fun m => Cmod (g m)) S).
Proof.
  intros g L; induction L as [|r L IH]; intros S Hndl Hnds Hincl.
  - assert (S = []).
    { destruct S as [|a S0]; [ reflexivity | exfalso; destruct (Hincl a (in_eq a S0)) ]. }
    subst; cbn [map]; unfold Cwsum, Rlsum; cbn [fold_right].
    replace (Cminus C0 C0) with C0 by ring; rewrite Cmod_C0; lra.
  - inversion Hndl as [| ? ? Hnin Hndl']; subst.
    cbn [map]; rewrite Cwsum_cons, Rlsum_cons.
    destruct (in_dec Nat.eq_dec r S) as [Hin | Hnin2].
    + rewrite (Cwsum_remove g r S Hin Hnds).
      rewrite (sum_remove (fun m => Cmod (g m)) r S Hin Hnds).
      replace (Cminus (Cadd (g r) (Cwsum (map g L)))
                      (Cadd (g r) (Cwsum (map g (remove Nat.eq_dec r S)))))
        with (Cminus (Cwsum (map g L)) (Cwsum (map g (remove Nat.eq_dec r S)))) by ring.
      replace (Cmod (g r) + Rlsum (map (fun m => Cmod (g m)) L) -
               (Cmod (g r) + Rlsum (map (fun m => Cmod (g m)) (remove Nat.eq_dec r S))))
        with (Rlsum (map (fun m => Cmod (g m)) L) -
              Rlsum (map (fun m => Cmod (g m)) (remove Nat.eq_dec r S))) by ring.
      apply IH; [ exact Hndl' | apply remove_nodup; exact Hnds | ].
      intros x Hx; apply in_remove in Hx; destruct Hx as [Hx1 Hx2].
      destruct (Hincl x Hx1) as [He | Hin']; [ exfalso; apply Hx2; symmetry; exact He | exact Hin' ].
    + assert (Hincl' : incl S L).
      { intros x Hx; destruct (Hincl x Hx) as [He | Hin']; [ subst r; contradiction | exact Hin' ]. }
      replace (Cminus (Cadd (g r) (Cwsum (map g L))) (Cwsum (map g S)))
        with (Cadd (g r) (Cminus (Cwsum (map g L)) (Cwsum (map g S)))) by ring.
      eapply Rle_trans; [ apply Cmod_triangle | ].
      replace (Cmod (g r) + Rlsum (map (fun m => Cmod (g m)) L) -
               Rlsum (map (fun m => Cmod (g m)) S))
        with (Cmod (g r) + (Rlsum (map (fun m => Cmod (g m)) L) -
                            Rlsum (map (fun m => Cmod (g m)) S))) by ring.
      apply Rplus_le_compat_l; apply IH; [ exact Hndl' | exact Hnds | exact Hincl' ].
Qed.

(* Cpsum a N as a Cwsum over [0..N] *)
Lemma Cpsum_Cwsum : forall a N, Cpsum a N = Cwsum (map a (seq 0 (S N))).
Proof.
  intros a N; induction N as [|N IH].
  - unfold Cwsum; cbn [Cpsum seq map fold_right]; ring.
  - cbn [Cpsum]; rewrite IH, (seq_S (S N) 0), map_app, Cwsum_app.
    replace (0 + S N)%nat with (S N) by lia.
    replace (Cwsum (map a [S N])) with (a (S N))
      by (unfold Cwsum; cbn [map fold_right]; ring).
    reflexivity.
Qed.

(* IZR of a nonneg Z is the INR of its Z.to_nat *)
Lemma IZR_INR_Z2Nat : forall c, (0 <= c)%Z -> IZR c = INR (Z.to_nat c).
Proof. intros c Hc; rewrite INR_IZR_INZ, Z2Nat.id by exact Hc; reflexivity. Qed.

(* a complex-limit sandwich: |u n - l| <= e n -> 0 ⇒ u -> l *)
Lemma CUn_cv_bound : forall u l e,
  (forall n, Cmod (Cminus (u n) l) <= e n) -> Un_cv e 0 -> CUn_cv u l.
Proof.
  intros u l e Hb He eps Heps; destruct (He eps Heps) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); unfold R_dist in HN; rewrite Rminus_0_r in HN.
  eapply Rle_lt_trans; [ apply Hb | eapply Rle_lt_trans; [ apply Rle_abs | exact HN ] ].
Qed.

(* ================================================================= *)
(*  the s-dependent argument                                          *)
(* ================================================================= *)

Section Conv.
Variable s : C.
Hypothesis Hgt : 1 < Re s.

Let sig := Re s.
Lemma Hsig0 : 0 < sig. Proof. unfold sig; lra. Qed.
Lemma Hsig1 : sig <> 1. Proof. unfold sig; lra. Qed.
Lemma Hsiggt : 1 < sig. Proof. unfold sig; exact Hgt. Qed.

(* the truncated complex Euler product over the primes ≤ S N *)
Definition cEF (N : nat) : C :=
  Cwprod (map (fun p => Csum (fun k => Cpow (Cpw (IZR p) (Copp s)) k) (S N))
              (primes_upto (S N))).

(* g m = m^{-s} as a complex number; its modulus is z sig m for m ≥ 1 *)
Definition cg (m : nat) : C := Cpw (INR m) (Copp s).

Lemma Cmod_cg : forall m, (1 <= m)%nat -> Cmod (cg m) = z sig m.
Proof.
  intros m Hm; unfold cg, z; rewrite Cpw_mod.
  destruct (Nat.eqb m 0) eqn:E; [ apply Nat.eqb_eq in E; lia | ].
  f_equal; unfold sig, Copp; cbn [Re]; ring.
Qed.

(* cEF reindexed: the truncated product = Cwsum of cg over the coded numbers *)
Lemma cEF_reindex : forall N,
  cEF N = Cwsum (map cg (map (fun ks => Z.to_nat (code (primes_upto (S N)) ks))
                              (gstates (map fug (primes_upto (S N))) (S N)))).
Proof.
  intro N; unfold cEF.
  rewrite (Ceuler_reindex_fin s (primes_upto (S N)) (S N) (primes_upto_Forall (S N))).
  rewrite map_map; apply Cwsum_map_ext; intro ks.
  unfold cg; f_equal.
  apply IZR_INR_Z2Nat.
  pose proof (code_pos (primes_upto (S N)) ks (primes_upto_Forall (S N))); lia.
Qed.

(* the coded numbers include every n ∈ [1 .. S N] (factorization existence) *)
Lemma incl_seq_codes : forall N,
  incl (seq 1 (S N))
       (map (fun ks => Z.to_nat (code (primes_upto (S N)) ks))
            (gstates (map fug (primes_upto (S N))) (S N))).
Proof.
  intro N; set (ps := primes_upto (S N)).
  assert (Hpr : Forall prime ps) by apply primes_upto_Forall.
  assert (Hnd : NoDup ps) by apply primes_upto_nodup.
  assert (Hpr2 : Forall (fun p => (2 <= p)%Z) ps).
  { apply Forall_impl with (P := prime); [ intros p Hp; destruct Hp; lia | exact Hpr ]. }
  intros m Hm; apply in_seq in Hm; destruct Hm as [Hm1 HmN].
  assert (Hsm : forall q, prime q -> (q | Z.of_nat m)%Z -> In q ps).
  { intros q Hq Hdvd; apply (small_smooth N m); [ lia | lia | exact Hq | exact Hdvd ]. }
  destruct (code_surj ps Hpr Hnd (Z.of_nat m) ltac:(lia) Hsm) as [ks [Hlen Hcode]].
  assert (Hb : Forall (fun e => (e < S N)%nat) ks).
  { apply Forall_forall; intros e He.
    pose proof (entry_pow_le_code ps ks Hpr2 Hlen e He) as Hpow.
    rewrite Hcode in Hpow.
    assert (Hpow2 : (2 ^ e <= m)%nat).
    { apply (proj2 (Nat2Z.inj_le (2 ^ e) m)); rewrite Nat2Z.inj_pow; exact Hpow. }
    pose proof (nat_lt_pow2 e); lia. }
  apply in_map_iff; exists ks; split.
  - rewrite Hcode, Nat2Z.id; reflexivity.
  - apply gstates_complete; [ rewrite length_map; symmetry; exact Hlen | exact Hb ].
Qed.

(* Σ_{n≤S N} n^{-s} as a Cwsum over [1 .. S N], = the Dirichlet partial sum *)
Lemma Cpsum_cterm_seq : forall N,
  Cpsum (cterm s) N = Cwsum (map cg (seq 1 (S N))).
Proof.
  intro N; rewrite Cpsum_Cwsum.
  replace (seq 1 (S N)) with (map S (seq 0 (S N)))
    by (rewrite <- seq_shift; reflexivity).
  rewrite map_map; apply Cwsum_map_ext; intro k; unfold cterm, cg, gC; reflexivity.
Qed.

(* the real gap of the moduli of the coded numbers vs [1..S N] → 0 *)
Lemma cEF_diff_bound : forall N,
  Cmod (Cminus (cEF N) (Cpsum (cterm s) N))
  <= zeta_cont sig Hsig0 Hsig1 - diag_trace (z sig) (S N).
Proof.
  intro N; set (ps := primes_upto (S N)).
  set (codes := map (fun ks => Z.to_nat (code ps ks))
                    (gstates (map fug ps) (S N))).
  assert (Hndc : NoDup codes) by (apply (codes_nat_nodup ps (primes_upto_Forall _) (primes_upto_nodup _))).
  assert (Hposc : forall m, In m codes -> (1 <= m)%nat)
    by (apply (codes_nat_pos ps (primes_upto_Forall _))).
  assert (Hposs : forall m, In m (seq 1 (S N)) -> (1 <= m)%nat)
    by (intros m Hm; apply in_seq in Hm; lia).
  rewrite (cEF_reindex N), (Cpsum_cterm_seq N).
  (* modulus of the missing part ≤ real gap of the moduli *)
  eapply Rle_trans;
    [ apply (Cmod_Cwsum_incl_diff cg codes (seq 1 (S N)) Hndc (seq_NoDup _ _) (incl_seq_codes N)) | ].
  (* rewrite the two real modulus-sums as z sig sums *)
  assert (HL : Rlsum (map (fun m => Cmod (cg m)) codes) = Rlsum (map (z sig) codes)).
  { f_equal; apply map_ext_in; intros m Hm; apply Cmod_cg; apply Hposc; exact Hm. }
  assert (HS : Rlsum (map (fun m => Cmod (cg m)) (seq 1 (S N)))
             = Rlsum (map (z sig) (seq 1 (S N)))).
  { f_equal; apply map_ext_in; intros m Hm; apply Cmod_cg; apply Hposs; exact Hm. }
  rewrite HL, HS.
  (* Rlsum (map (z sig) codes) ≤ zeta_cont sig ; the seq sum = diag_trace *)
  assert (Hup : Rlsum (map (z sig) codes) <= zeta_cont sig Hsig0 Hsig1)
    by (apply (recip_s_nodup_bound sig Hsig0 Hsig1 Hsiggt); [ exact Hndc | exact Hposc ]).
  assert (Hdt : Rlsum (map (z sig) (seq 1 (S N))) = diag_trace (z sig) (S N))
    by (unfold Rlsum; symmetry; apply diag_trace_eq).
  rewrite Hdt; lra.
Qed.

(* the real gap → 0 *)
Lemma gap_cv0 : Un_cv (fun N => zeta_cont sig Hsig0 Hsig1 - diag_trace (z sig) (S N)) 0.
Proof.
  replace 0 with (zeta_cont sig Hsig0 Hsig1 - zeta_cont sig Hsig0 Hsig1) by ring.
  apply CV_minus; [ apply Un_cv_const | ].
  apply (Un_cv_S (fun N => diag_trace (z sig) N)).
  apply (operator_zeta_eq_cont sig Hsig0 Hsig1 Hsiggt).
Qed.

(* THE CONVERGENCE: the truncated complex Euler product → zetaC s *)
Theorem cEF_cv : forall (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  CUn_cv cEF (zetaC s H0 H1).
Proof.
  intros H0 H1.
  apply (CUn_cv_bound cEF (zetaC s H0 H1)
           (fun N => (zeta_cont sig Hsig0 Hsig1 - diag_trace (z sig) (S N))
                     + Cmod (Cminus (Cpsum (cterm s) N) (zetaC s H0 H1)))).
  - intro N.
    replace (Cminus (cEF N) (zetaC s H0 H1))
      with (Cadd (Cminus (cEF N) (Cpsum (cterm s) N))
                 (Cminus (Cpsum (cterm s) N) (zetaC s H0 H1))) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    apply Rplus_le_compat; [ apply cEF_diff_bound | apply Rle_refl ].
  - replace 0 with (0 + 0) by ring; apply CV_plus; [ apply gap_cv0 | ].
    (* Cmod (Cpsum (cterm s) N − zetaC s) → 0  from CDirichlet.zetaC_eq_dirichlet *)
    intros eps Heps.
    destruct (zetaC_eq_dirichlet s H0 H1 Hgt eps Heps) as [N HN]; exists N; intros n Hn.
    specialize (HN n Hn); unfold R_dist; rewrite Rminus_0_r.
    rewrite Rabs_right by (apply Rle_ge, Cmod_nonneg); exact HN.
Qed.

End Conv.

Print Assumptions cEF_cv.

(* ================================================================= *)
(*  END CEulerProductConv.v                                           *)
(* ================================================================= *)
