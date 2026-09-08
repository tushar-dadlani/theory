(* ================================================================= *)
(*  CTwistedSmooth.v  --  truncated twisted product -> the L-series.   *)
(*                                                                    *)
(*  The analogue of CEulerProductConv's Section Conv for the character *)
(*  twist.  Everything coefficient-free there is imported unchanged;   *)
(*  in particular incl_seq_codes (every n <= N is smooth over the      *)
(*  primes <= N) exports with no s argument and is reused verbatim.    *)
(*                                                                    *)
(*  THE ONE THING THAT CANNOT BE REUSED is Cmod_Cwsum_incl_diff:       *)
(*                                                                    *)
(*    Cmod (Cwsum (map g L) - Cwsum (map g S))                         *)
(*      <= Rlsum (map (fun m => Cmod (g m)) L)                         *)
(*         - Rlsum (map (fun m => Cmod (g m)) S)                       *)
(*                                                                    *)
(*  Cmod (g m) occurs on BOTH sides of the subtraction.  For zeta that *)
(*  is harmless: Cmod_cg is an EQUALITY, so both occurrences rewrite.  *)
(*  For the twist only Cmod (chi(m) m^{-s}) <= z sig m holds -- and it *)
(*  is 0 exactly on the modulus -- so the S-side would need the        *)
(*  inequality in the wrong direction.  The majorant form below fixes  *)
(*  it; the induction is unchanged apart from applying sum_remove to h *)
(*  rather than to Cmod o g, and Rplus_le_compat_l -> Rplus_le_compat. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List QArith.
Require Import ComplexField Cmodulus CexpFull CPowMul CPowBase CSeries
        RootsOfUnity DirichletLEuler PrimonGas PrimeFactorizationN
        EulerReindex EulerProductR EulerProductZeta EulerProductZetaBound
        EulerProductZetaCont CEulerProductFull
        RecipSquareBound Ell2Zeta Ell2ZetaCont ZmodOrder DirichletModP
        CharModulus CEulerReindexGen CTwistedCoeff CLSeries
        CEulerFactorSmooth CEulerProductConv.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  the majorant form of the inclusion-difference bound                *)
(* ----------------------------------------------------------------- *)
Lemma Cmod_Cwsum_incl_diff_maj : forall (g : nat -> C) (h : nat -> R) L S,
  (forall m, In m L -> Cmod (g m) <= h m) ->
  NoDup L -> NoDup S -> incl S L ->
  Cmod (Cminus (Cwsum (map g L)) (Cwsum (map g S)))
  <= Rlsum (map h L) - Rlsum (map h S).
Proof.
  intros g h L; induction L as [| r L IH]; intros S Hmaj Hndl Hnds Hincl.
  - assert (HS : S = []).
    { destruct S as [| b S0]; [ reflexivity | exfalso; destruct (Hincl b (in_eq b S0)) ]. }
    subst; cbn [map]; unfold Cwsum, Rlsum; cbn [fold_right].
    replace (Cminus C0 C0) with C0 by ring; rewrite Cmod_C0; lra.
  - inversion Hndl as [| ? ? Hnin Hndl']; subst.
    cbn [map]; rewrite Cwsum_cons, Rlsum_cons.
    assert (Hmaj' : forall m, In m L -> Cmod (g m) <= h m)
      by (intros m Hm; apply Hmaj; right; exact Hm).
    destruct (in_dec Nat.eq_dec r S) as [Hin | Hnin2].
    + rewrite (Cwsum_remove g r S Hin Hnds).
      rewrite (sum_remove h r S Hin Hnds).
      replace (Cminus (Cadd (g r) (Cwsum (map g L)))
                      (Cadd (g r) (Cwsum (map g (remove Nat.eq_dec r S)))))
        with (Cminus (Cwsum (map g L)) (Cwsum (map g (remove Nat.eq_dec r S)))) by ring.
      replace (h r + Rlsum (map h L)
               - (h r + Rlsum (map h (remove Nat.eq_dec r S))))
        with (Rlsum (map h L) - Rlsum (map h (remove Nat.eq_dec r S))) by ring.
      apply IH; [ exact Hmaj' | exact Hndl' | apply remove_nodup; exact Hnds | ].
      intros x Hx; apply in_remove in Hx; destruct Hx as [Hx1 Hx2].
      destruct (Hincl x Hx1) as [He | Hin'];
        [ exfalso; apply Hx2; symmetry; exact He | exact Hin' ].
    + assert (Hincl' : incl S L).
      { intros x Hx; destruct (Hincl x Hx) as [He | Hin'];
          [ subst r; contradiction | exact Hin' ]. }
      replace (Cminus (Cadd (g r) (Cwsum (map g L))) (Cwsum (map g S)))
        with (Cadd (g r) (Cminus (Cwsum (map g L)) (Cwsum (map g S)))) by ring.
      eapply Rle_trans; [ apply Cmod_triangle | ].
      replace (h r + Rlsum (map h L) - Rlsum (map h S))
        with (h r + (Rlsum (map h L) - Rlsum (map h S))) by ring.
      apply Rplus_le_compat;
        [ apply Hmaj; left; reflexivity
        | apply IH; [ exact Hmaj' | exact Hndl' | exact Hnds | exact Hincl' ] ].
Qed.

(* ================================================================= *)
Section TwSmooth.

Variable p g a : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.

Variable s : C.
Hypothesis Hgt : 1 < Re s.

Lemma HsA0 : 0 < Re s. Proof. lra. Qed.
Lemma HsA1 : Re s <> 1. Proof. lra. Qed.
Lemma HsAgt : 1 < Re s. Proof. exact Hgt. Qed.

(* the truncated twisted Euler product over the primes <= S N *)
Definition cLF (N : nat) : C :=
  Cwprod (map (fun q => Csum (fun k => Cpow (Fchi p g a s q) k) (S N))
              (primes_upto (S N))).

Lemma cLF_reindex : forall N,
  cLF N = Cwsum (map (Gchi p g a s)
                     (map (fun ks => Z.to_nat (code (primes_upto (S N)) ks))
                          (gstates (map fug (primes_upto (S N))) (S N)))).
Proof.
  intro N; unfold cLF.
  rewrite (Ceuler_reindex_gen (Fchi p g a s)
             (Fchi_1 p g a Hp Hg Hord s)
             (Fchi_mul p g a Hp Hg Hord s)
             (primes_upto (S N)) (S N) (primes_upto_Forall (S N))).
  rewrite map_map; apply Cwsum_map_ext; intro ks.
  set (c := code (primes_upto (S N)) ks).
  assert (Hc : (0 <= c)%Z)
    by (unfold c; pose proof (code_pos (primes_upto (S N)) ks
                                (primes_upto_Forall (S N))); lia).
  rewrite <- (Fchi_nat p g a s (Z.to_nat c)), (Z2Nat.id c Hc). reflexivity.
Qed.

Lemma Cpsum_Lterm_seq : forall N,
  Cpsum (Lterm p g a s) N = Cwsum (map (Gchi p g a s) (seq 1 (S N))).
Proof.
  intro N; rewrite Cpsum_Cwsum.
  replace (seq 1 (S N)) with (map S (seq 0 (S N)))
    by (rewrite <- seq_shift; reflexivity).
  rewrite map_map; apply Cwsum_map_ext; intro k; unfold Lterm; reflexivity.
Qed.

Lemma cLF_diff_bound : forall N,
  Cmod (Cminus (cLF N) (Cpsum (Lterm p g a s) N))
  <= zeta_cont (Re s) HsA0 HsA1 - diag_trace (z (Re s)) (S N).
Proof.
  intro N; set (ps := primes_upto (S N)).
  set (codes := map (fun ks => Z.to_nat (code ps ks))
                    (gstates (map fug ps) (S N))).
  assert (Hndc : NoDup codes)
    by (apply (codes_nat_nodup ps (primes_upto_Forall _) (primes_upto_nodup _))).
  assert (Hposc : forall m, In m codes -> (1 <= m)%nat)
    by (apply (codes_nat_pos ps (primes_upto_Forall _))).
  rewrite (cLF_reindex N), (Cpsum_Lterm_seq N).
  eapply Rle_trans;
    [ apply (Cmod_Cwsum_incl_diff_maj (Gchi p g a s) (z (Re s))
               codes (seq 1 (S N))
               (fun m _ => Gchi_mod_le p g a Hg Hord s m)
               Hndc (seq_NoDup _ _) (incl_seq_codes N)) | ].
  assert (Hup : Rlsum (map (z (Re s)) codes) <= zeta_cont (Re s) HsA0 HsA1)
    by (apply (recip_s_nodup_bound (Re s) HsA0 HsA1 HsAgt);
        [ exact Hndc | exact Hposc ]).
  assert (Hdt : Rlsum (map (z (Re s)) (seq 1 (S N)))
                = diag_trace (z (Re s)) (S N))
    by (unfold Rlsum; symmetry; apply diag_trace_eq).
  rewrite Hdt; lra.
Qed.

Lemma gapL_cv0 :
  Un_cv (fun N => zeta_cont (Re s) HsA0 HsA1 - diag_trace (z (Re s)) (S N)) 0.
Proof.
  replace 0 with (zeta_cont (Re s) HsA0 HsA1 - zeta_cont (Re s) HsA0 HsA1) by ring.
  apply CV_minus; [ apply Un_cv_const | ].
  apply (Un_cv_S (fun N => diag_trace (z (Re s)) N)).
  apply (operator_zeta_eq_cont (Re s) HsA0 HsA1 HsAgt).
Qed.

(* the truncated twisted Euler product converges to the L-series *)
Theorem cLF_cv : forall Lval, Cseries_cv (Lterm p g a s) Lval -> CUn_cv cLF Lval.
Proof.
  intros Lval HL.
  apply (CUn_cv_bound cLF Lval
           (fun N => (zeta_cont (Re s) HsA0 HsA1 - diag_trace (z (Re s)) (S N))
                     + Cmod (Cminus (Cpsum (Lterm p g a s) N) Lval))).
  - intro N.
    replace (Cminus (cLF N) Lval)
      with (Cadd (Cminus (cLF N) (Cpsum (Lterm p g a s) N))
                 (Cminus (Cpsum (Lterm p g a s) N) Lval)) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    apply Rplus_le_compat; [ apply cLF_diff_bound | apply Rle_refl ].
  - replace 0 with (0 + 0) by ring; apply CV_plus; [ apply gapL_cv0 | ].
    intros eps Heps. destruct (HL eps Heps) as [N HN]; exists N; intros n Hn.
    specialize (HN n Hn); unfold R_dist; rewrite Rminus_0_r.
    rewrite Rabs_right by (apply Rle_ge, Cmod_nonneg); exact HN.
Qed.

End TwSmooth.

Print Assumptions cLF_cv.

(* ================================================================= *)
(*  END CTwistedSmooth.v                                              *)
(* ================================================================= *)
