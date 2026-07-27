(* ================================================================= *)
(*  DFTConvolution.v                                                 *)
(*                                                                    *)
(*  THE CONVOLUTION THEOREM for the complex DFT on the custom C.      *)
(*                                                                    *)
(*  Cyclic convolution  (f * g)(n) = sum_{k<N} f k * g((n-k) mod N)   *)
(*  transforms to the POINTWISE PRODUCT of the transforms:            *)
(*                                                                    *)
(*     conv_theorem :  DFT (f * g) m = DFT f m * DFT g m.             *)
(*                                                                    *)
(*  Together with DFTInversion (F^{-1}F = id) this is the full        *)
(*  algebraic toolkit: the DFT DIAGONALISES cyclic convolution.       *)
(*                                                                    *)
(*  The one genuinely new ingredient is that a CYCLIC SHIFT permutes   *)
(*  the index set {0,...,N-1} (rotation_perm), giving the reindexing   *)
(*  lemma Csum_reindex; combined with the periodicity of the root      *)
(*  (Cpow_wc_mod: (wc N)^a depends only on a mod N) it yields the      *)
(*  shift theorem dft_shift, and the convolution theorem then follows  *)
(*  by finite Fubini (Csum_swap) + scalar factoring -- all C-field     *)
(*  algebra.                                                          *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via C / trig).      *)
(* ================================================================= *)

From Stdlib Require Import Reals Arith Lia Lra List Permutation QArith Qcanon.
Import ListNotations.
Require Import QPoly QPolyEmbed QPolyCoeffPIT QPolyQuot CycloOrthogonality.
Require Import ComplexField RootsOfUnity DFTInversion.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Root periodicity:  (wc N)^a  depends only on  a mod N            *)
(* ----------------------------------------------------------------- *)

Lemma Cpow_wc_mod : forall N a, (0 < N)%nat -> Cpow (wc N) a = Cpow (wc N) (a mod N).
Proof.
  intros N a HN.
  rewrite (Nat.div_mod_eq a N) at 1.
  rewrite Cpow_add, Cpow_mul, (wc_pow_N N HN), Cpow_C1; ring.
Qed.

(* the exponent congruence used by the shift theorem *)
Lemma exp_cong : forall N m n k, (0 < N)%nat -> (k <= N)%nat ->
  (m * k + m * ((n + N - k) mod N)) mod N = (m * n) mod N.
Proof.
  intros N m n k HN Hk.
  assert (Hkj : (k + (n + N - k) mod N) mod N = n mod N).
  { rewrite Nat.Div0.add_mod_idemp_r.
    replace (k + (n + N - k))%nat with (n + 1 * N)%nat by lia.
    apply Nat.Div0.mod_add. }
  replace (m * k + m * ((n + N - k) mod N))%nat
    with (m * (k + (n + N - k) mod N))%nat by ring.
  rewrite <- (Nat.Div0.mul_mod_idemp_r m (k + (n + N - k) mod N)), Hkj.
  apply Nat.Div0.mul_mod_idemp_r.
Qed.

(* ----------------------------------------------------------------- *)
(*  A cyclic shift permutes {0,...,N-1}  =>  reindexing lemma         *)
(* ----------------------------------------------------------------- *)

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hinj Hnd; simpl; [ constructor | ].
  rewrite NoDup_cons_iff in Hnd; destruct Hnd as [Hna Hnd].
  rewrite NoDup_cons_iff; split.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Hfy Hy]].
    assert (a = y) by (apply Hinj; [ left; reflexivity | right; exact Hy | symmetry; exact Hfy ]).
    subst y; contradiction.
  - apply IH; [ intros x y Hx Hy; apply Hinj; right; assumption | exact Hnd ].
Qed.

Lemma mod_wrap : forall N x, (N <= x)%nat -> (x < 2 * N)%nat -> x mod N = (x - N)%nat.
Proof.
  intros N x H1 H2; transitivity ((x - N) mod N).
  - replace x with ((x - N) + 1 * N)%nat at 1 by lia; apply Nat.Div0.mod_add.
  - apply Nat.mod_small; lia.
Qed.

Lemma mod_add_r_inj : forall N a b r, (a < N)%nat -> (b < N)%nat -> (r < N)%nat ->
  (a + r) mod N = (b + r) mod N -> a = b.
Proof.
  intros N a b r Ha Hb Hr H.
  destruct (Nat.lt_ge_cases (a + r) N) as [HaN|HaN];
  destruct (Nat.lt_ge_cases (b + r) N) as [HbN|HbN];
  [ rewrite (Nat.mod_small _ _ HaN), (Nat.mod_small _ _ HbN) in H
  | rewrite (Nat.mod_small _ _ HaN), (mod_wrap N (b + r) HbN ltac:(lia)) in H
  | rewrite (mod_wrap N (a + r) HaN ltac:(lia)), (Nat.mod_small _ _ HbN) in H
  | rewrite (mod_wrap N (a + r) HaN ltac:(lia)), (mod_wrap N (b + r) HbN ltac:(lia)) in H ];
  lia.
Qed.

Lemma shift_mod_inj : forall N c a b, (0 < N)%nat -> (a < N)%nat -> (b < N)%nat ->
  (a + c) mod N = (b + c) mod N -> a = b.
Proof.
  intros N c a b HN Ha Hb H.
  apply (mod_add_r_inj N a b (c mod N)); [ lia | lia | apply Nat.mod_upper_bound; lia | ].
  rewrite !Nat.Div0.add_mod_idemp_r; exact H.
Qed.

Lemma rotation_perm : forall N c,
  Permutation (map (fun n => (n + c) mod N) (seq 0 N)) (seq 0 N).
Proof.
  intros N c; destruct (Nat.eq_dec N 0) as [->|HN].
  - simpl; apply Permutation_refl.
  - apply NoDup_Permutation_bis.
    + apply NoDup_map_inj; [ | apply seq_NoDup ].
      intros a b Ha Hb Hab; apply in_seq in Ha; apply in_seq in Hb.
      apply (shift_mod_inj N c a b); [ lia | lia | lia | exact Hab ].
    + rewrite length_map, !length_seq; lia.
    + intros x Hx; apply in_map_iff in Hx as [n [Hn _]].
      apply in_seq; split; [ lia | ].
      rewrite <- Hn; apply Nat.mod_upper_bound; lia.
Qed.

(* --- Csum <-> fold bridge, and permutation-invariance of the fold --- *)

Lemma fold_snoc : forall L x, fold_right Cadd C0 (L ++ [x]) = Cadd (fold_right Cadd C0 L) x.
Proof. intros L x; induction L as [|y L IH]; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma Csum_fold : forall f N, Csum f N = fold_right Cadd C0 (map f (seq 0 N)).
Proof.
  intros f N; induction N as [|N IH]; [ reflexivity | ].
  cbn [Csum]; rewrite IH, seq_S, map_app; cbn [map].
  rewrite fold_snoc; replace (0 + N)%nat with N by lia; reflexivity.
Qed.

Lemma fold_Cadd_perm : forall l1 l2, Permutation l1 l2 ->
  fold_right Cadd C0 l1 = fold_right Cadd C0 l2.
Proof.
  intros l1 l2 Hp; induction Hp; simpl.
  - reflexivity.
  - rewrite IHHp; reflexivity.
  - ring.
  - rewrite IHHp1, IHHp2; reflexivity.
Qed.

Lemma Csum_reindex : forall (phi : nat -> C) N c,
  Csum (fun n => phi ((n + c) mod N)) N = Csum phi N.
Proof.
  intros phi N c.
  rewrite (Csum_fold (fun n => phi ((n + c) mod N)) N), (Csum_fold phi N).
  rewrite <- (map_map (fun n => (n + c) mod N) phi).
  apply fold_Cadd_perm, Permutation_map, rotation_perm.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE SHIFT THEOREM                                                *)
(*    sum_n g((n+N-k) mod N) (wc N)^(m n) = (wc N)^(m k) * DFT g m     *)
(* ----------------------------------------------------------------- *)

Lemma dft_shift : forall N m k g, (0 < N)%nat -> (k <= N)%nat ->
  Csum (fun n => Cmul (g ((n + N - k) mod N)) (Cpow (wc N) (m * n))) N
  = Cmul (Cpow (wc N) (m * k))
         (Csum (fun j => Cmul (g j) (Cpow (wc N) (m * j))) N).
Proof.
  intros N m k g HN Hk.
  rewrite (Csum_ext
    (fun n => Cmul (g ((n + N - k) mod N)) (Cpow (wc N) (m * n)))
    (fun n => Cmul (Cpow (wc N) (m * k))
                   (Cmul (g ((n + N - k) mod N))
                         (Cpow (wc N) (m * ((n + N - k) mod N))))) N).
  2:{ intro n.
      transitivity (Cmul (g ((n + N - k) mod N))
                         (Cpow (wc N) (m * k + m * ((n + N - k) mod N)))).
      - f_equal.
        rewrite (Cpow_wc_mod N (m * n) HN),
                (Cpow_wc_mod N (m * k + m * ((n + N - k) mod N)) HN).
        f_equal; symmetry; apply exp_cong; assumption.
      - rewrite Cpow_add; ring. }
  rewrite <- Csum_scale_l; f_equal.
  rewrite (Csum_ext
    (fun n => Cmul (g ((n + N - k) mod N)) (Cpow (wc N) (m * ((n + N - k) mod N))))
    (fun n => (fun j => Cmul (g j) (Cpow (wc N) (m * j))) ((n + (N - k)) mod N)) N)
    by (intro n; replace (n + N - k)%nat with (n + (N - k))%nat by lia; reflexivity).
  apply (Csum_reindex (fun j => Cmul (g j) (Cpow (wc N) (m * j))) N (N - k)).
Qed.

(* ----------------------------------------------------------------- *)
(*  CYCLIC CONVOLUTION AND THE CONVOLUTION THEOREM                   *)
(* ----------------------------------------------------------------- *)

Definition Cconv (N : nat) (f g : nat -> C) (n : nat) : C :=
  Csum (fun k => Cmul (f k) (g ((n + N - k) mod N))) N.

Theorem conv_theorem : forall N f g m, (0 < N)%nat ->
  DFT N (Cconv N f g) m = Cmul (DFT N f m) (DFT N g m).
Proof.
  intros N f g m HN.
  unfold DFT, Cconv.
  (* push (wc N)^(m n) into the inner k-sum *)
  rewrite (Csum_ext
    (fun n => Cmul (Csum (fun k => Cmul (f k) (g ((n + N - k) mod N))) N)
                   (Cpow (wc N) (m * n)))
    (fun n => Csum (fun k => Cmul (Cmul (f k) (g ((n + N - k) mod N)))
                                  (Cpow (wc N) (m * n))) N) N)
    by (intro n; apply Csum_scale_r).
  (* finite Fubini: swap n and k *)
  rewrite (Csum_swap
    (fun n k => Cmul (Cmul (f k) (g ((n + N - k) mod N))) (Cpow (wc N) (m * n))) N N).
  (* for each k<N: factor f k out and apply the shift theorem *)
  rewrite (Csum_ext_bounded
    (fun k => Csum (fun n => Cmul (Cmul (f k) (g ((n + N - k) mod N)))
                                  (Cpow (wc N) (m * n))) N)
    (fun k => Cmul (Cmul (f k) (Cpow (wc N) (m * k)))
                   (Csum (fun j => Cmul (g j) (Cpow (wc N) (m * j))) N)) N).
  2:{ intros k Hk.
      rewrite (Csum_ext
        (fun n => Cmul (Cmul (f k) (g ((n + N - k) mod N))) (Cpow (wc N) (m * n)))
        (fun n => Cmul (f k) (Cmul (g ((n + N - k) mod N)) (Cpow (wc N) (m * n)))) N)
        by (intro n; ring).
      rewrite <- Csum_scale_l, (dft_shift N m k g HN ltac:(lia)); ring. }
  (* factor the constant DFT g m out of the k-sum *)
  rewrite <- (Csum_scale_r
    (Csum (fun j => Cmul (g j) (Cpow (wc N) (m * j))) N)
    (fun k => Cmul (f k) (Cpow (wc N) (m * k))) N).
  reflexivity.
Qed.

Print Assumptions conv_theorem.

(* ================================================================================= *)
(*  THE AXIOM-FREE ALGEBRAIC CONVOLUTION THEOREM, over R = ℚ[x]/(Φ_N).                *)
(*  DFT_R (f ⊛ g) = DFT_R f · DFT_R g, with the transcendental root replaced by ζ.    *)
(*  Reuses the nat-level cyclic-shift permutation (rotation_perm) above and the       *)
(*  req-plumbing from DFTInversion; the reindexing goes through a fold/permutation    *)
(*  bridge over req.  Print Assumptions = Closed under the global context.            *)
(* ================================================================================= *)

Section RCONV.
  Variable Nn : nat.
  Hypothesis HN : (1 <= Nn)%nat.
  Local Open Scope Qc_scope.
  Notation Rq := (req Nn).

  (* generic exact rpow identities over R *)
  Lemma rpow_add_r : forall b i j, Rq (rpow b (i + j)) (qmul (rpow b i) (rpow b j)).
  Proof. intros; apply req_of_qeval; intro x; rewrite qeval_mul, !qeval_rpow, Qcpow_add; reflexivity. Qed.
  Lemma rpow_mul_r : forall b i j, Rq (rpow b (i * j)) (rpow (rpow b i) j).
  Proof. intros; apply req_of_qeval; intro x; rewrite !qeval_rpow, Qcpow_mul; reflexivity. Qed.

  (* periodicity for any base that is an N-th root of unity *)
  Lemma rpow_base_periodic : forall b, Rq (rpow b Nn) [1] ->
    forall a, Rq (rpow b a) (rpow b (a mod Nn)).
  Proof.
    intros b Hb a.
    apply (req_trans Nn _ (qmul (rpow b (Nn * (a / Nn))) (rpow b (a mod Nn))) _).
    - apply (req_trans Nn _ (rpow b (Nn * (a / Nn) + a mod Nn)) _).
      + rewrite <- (Nat.div_mod_eq a Nn); apply req_refl.
      + apply rpow_add_r.
    - apply (req_trans Nn _ (qmul [1] (rpow b (a mod Nn))) _).
      + apply req_qmul_r.
        apply (req_trans Nn _ (rpow (rpow b Nn) (a / Nn)) _);
          [ apply rpow_mul_r
          | apply (req_trans Nn _ (rpow [1] (a / Nn)) _);
            [ apply req_rpow; exact Hb
            | apply req_of_qeval; intro x; rewrite qeval_rpow, !qeval_one, Qcpow_1_l; reflexivity ] ].
      + apply req_of_qeval; intro x; rewrite qeval_mul, qeval_one; ring.
  Qed.

  (* the inverse root wcz = ζ^{N-1} is itself an N-th root of unity *)
  Lemma wcz_pow_N : Rq (rpow (wcz Nn) Nn) [1].
  Proof.
    unfold wcz.
    apply (req_trans Nn _ (rpow (rpow zeta Nn) (Nn - 1)) _).
    - apply req_of_qeval; intro x.
      rewrite (qeval_rpow (rpow zeta (Nn - 1)) Nn), (qeval_rpow (rpow zeta Nn) (Nn - 1)),
              !qeval_rpow_zeta, <- !Qcpow_mul.
      f_equal; nia.
    - apply (req_trans Nn _ (rpow [1] (Nn - 1)) _);
        [ apply req_rpow, zeta_pow_N; exact HN
        | apply req_of_qeval; intro x; rewrite qeval_rpow, !qeval_one, Qcpow_1_l; reflexivity ].
  Qed.

  Lemma rpow_wcz_mod : forall a, Rq (rpow (wcz Nn) a) (rpow (wcz Nn) (a mod Nn)).
  Proof. intro a; apply rpow_base_periodic, wcz_pow_N. Qed.

  (* ---- fold / permutation bridge for rsum (the req analogue of Csum_reindex) ---- *)
  Lemma fold_qadd_snoc : forall L x,
    Rq (fold_right qadd [] (L ++ [x])) (qadd (fold_right qadd [] L) x).
  Proof.
    intros L x; induction L as [|y L IH]; cbn [fold_right app].
    - apply req_of_qeval; intro pt; rewrite !qeval_add, qeval_nil; ring.
    - apply (req_trans Nn _ (qadd y (qadd (fold_right qadd [] L) x)) _).
      + apply req_qadd; [ apply req_refl | exact IH ].
      + apply req_of_qeval; intro pt; rewrite !qeval_add; ring.
  Qed.

  Lemma rsum_fold : forall f n, Rq (rsum f n) (fold_right qadd [] (map f (seq 0 n))).
  Proof.
    intros f n; induction n as [|n IH]; cbn [rsum].
    - apply req_refl.
    - rewrite seq_S, map_app; cbn [map].
      apply (req_trans Nn _ (qadd (fold_right qadd [] (map f (seq 0 n))) (f (0 + n)%nat)) _).
      + replace (0 + n)%nat with n by lia; apply req_qadd; [ exact IH | apply req_refl ].
      + apply req_sym, fold_qadd_snoc.
  Qed.

  Lemma fold_qadd_perm : forall l1 l2, Permutation l1 l2 ->
    Rq (fold_right qadd [] l1) (fold_right qadd [] l2).
  Proof.
    intros l1 l2 Hp; induction Hp; cbn [fold_right].
    - apply req_refl.
    - apply req_qadd; [ apply req_refl | exact IHHp ].
    - apply req_of_qeval; intro pt; rewrite !qeval_add; ring.
    - apply (req_trans Nn _ (fold_right qadd [] l') _); assumption.
  Qed.

  Lemma rsum_reindex : forall (phi : nat -> qpoly) c,
    Rq (rsum (fun n => phi ((n + c) mod Nn)) Nn) (rsum phi Nn).
  Proof.
    intros phi c.
    apply (req_trans Nn _ (fold_right qadd [] (map (fun n => phi ((n + c) mod Nn)) (seq 0 Nn))) _).
    { apply rsum_fold. }
    apply (req_trans Nn _ (fold_right qadd [] (map phi (seq 0 Nn))) _).
    2:{ apply req_sym, rsum_fold. }
    rewrite <- (map_map (fun n => (n + c) mod Nn) phi).
    apply fold_qadd_perm, Permutation_map, rotation_perm.
  Qed.

  (* ---- the shift theorem over R ---- *)
  Lemma dft_shift_R : forall m k g, (k <= Nn)%nat ->
    Rq (rsum (fun n => qmul (g ((n + Nn - k) mod Nn)) (rpow (wcz Nn) (m * n))) Nn)
       (qmul (rpow (wcz Nn) (m * k))
             (rsum (fun j => qmul (g j) (rpow (wcz Nn) (m * j))) Nn)).
  Proof.
    intros m k g Hk. assert (HNp : (0 < Nn)%nat) by lia.
    apply (req_trans Nn _
      (rsum (fun n => qmul (rpow (wcz Nn) (m * k))
              (qmul (g ((n + Nn - k) mod Nn)) (rpow (wcz Nn) (m * ((n + Nn - k) mod Nn))))) Nn) _).
    { apply (rsum_ext_bounded Nn HN); intros n _.
      apply (req_trans Nn _
        (qmul (g ((n + Nn - k) mod Nn)) (rpow (wcz Nn) (m * k + m * ((n + Nn - k) mod Nn)))) _).
      - apply req_qmul_l.
        apply (req_trans Nn _ (rpow (wcz Nn) ((m * n) mod Nn)) _); [ apply rpow_wcz_mod | ].
        apply (req_trans Nn _ (rpow (wcz Nn) ((m * k + m * ((n + Nn - k) mod Nn)) mod Nn)) _).
        + rewrite (exp_cong Nn m n k HNp Hk); apply req_refl.
        + apply req_sym, rpow_wcz_mod.
      - apply (req_trans Nn _
          (qmul (g ((n + Nn - k) mod Nn))
                (qmul (rpow (wcz Nn) (m * k)) (rpow (wcz Nn) (m * ((n + Nn - k) mod Nn))))) _).
        + apply req_qmul_l, rpow_add_r.
        + apply req_of_qeval; intro x; rewrite !qeval_mul; ring. }
    apply (req_trans Nn _
      (qmul (rpow (wcz Nn) (m * k))
            (rsum (fun n => qmul (g ((n + Nn - k) mod Nn)) (rpow (wcz Nn) (m * ((n + Nn - k) mod Nn)))) Nn)) _).
    { apply req_sym, rsum_scale_l. }
    apply req_qmul_l.
    apply (req_trans Nn _
      (rsum (fun n => (fun j => qmul (g j) (rpow (wcz Nn) (m * j))) ((n + (Nn - k)) mod Nn)) Nn) _).
    { apply (rsum_ext_bounded Nn HN); intros n _.
      replace (n + Nn - k)%nat with (n + (Nn - k))%nat by lia; apply req_refl. }
    apply (rsum_reindex (fun j => qmul (g j) (rpow (wcz Nn) (m * j))) (Nn - k)).
  Qed.

  Definition Cconv_R (f g : nat -> qpoly) (n : nat) : qpoly :=
    rsum (fun k => qmul (f k) (g ((n + Nn - k) mod Nn))) Nn.

  Theorem conv_theorem_R : forall f g m,
    Rq (DFT_R Nn (Cconv_R f g) m) (qmul (DFT_R Nn f m) (DFT_R Nn g m)).
  Proof.
    intros f g m. unfold DFT_R, Cconv_R.
    apply (req_trans Nn _
      (rsum (fun n => rsum (fun k =>
         qmul (qmul (f k) (g ((n + Nn - k) mod Nn))) (rpow (wcz Nn) (m * n))) Nn) Nn) _).
    { apply (rsum_ext_bounded Nn HN); intros n _; apply rsum_scale_r. }
    apply (req_trans Nn _
      (rsum (fun k => rsum (fun n =>
         qmul (qmul (f k) (g ((n + Nn - k) mod Nn))) (rpow (wcz Nn) (m * n))) Nn) Nn) _).
    { apply rsum_swap. }
    apply (req_trans Nn _
      (rsum (fun k => qmul (qmul (f k) (rpow (wcz Nn) (m * k)))
                           (rsum (fun j => qmul (g j) (rpow (wcz Nn) (m * j))) Nn)) Nn) _).
    { apply (rsum_ext_bounded Nn HN); intros k Hk.
      apply (req_trans Nn _
        (qmul (f k) (rsum (fun n => qmul (g ((n + Nn - k) mod Nn)) (rpow (wcz Nn) (m * n))) Nn)) _).
      - apply (req_trans Nn _
          (rsum (fun n => qmul (f k) (qmul (g ((n + Nn - k) mod Nn)) (rpow (wcz Nn) (m * n)))) Nn) _).
        + apply (rsum_ext_bounded Nn HN); intros n _; apply req_of_qeval; intro x; rewrite !qeval_mul; ring.
        + apply req_sym, rsum_scale_l.
      - apply (req_trans Nn _
          (qmul (f k) (qmul (rpow (wcz Nn) (m * k))
                            (rsum (fun j => qmul (g j) (rpow (wcz Nn) (m * j))) Nn))) _).
        + apply req_qmul_l, dft_shift_R; lia.
        + apply req_of_qeval; intro x; rewrite !qeval_mul; ring. }
    apply req_sym, rsum_scale_r.
  Qed.

End RCONV.

Print Assumptions conv_theorem_R.

(* ================================================================= *)
(*  END DFTConvolution.v                                             *)
(*  The complex DFT diagonalises cyclic convolution:                  *)
(*  DFT (f * g) = DFT f . DFT g.  With DFTInversion (F^{-1}F = id)     *)
(*  this completes the finite-Fourier toolkit on the custom field C.  *)
(*  The new content is the cyclic-shift permutation (rotation_perm)    *)
(*  + root periodicity (Cpow_wc_mod); the rest is finite Fubini and    *)
(*  C-field algebra.  Uses the classical Reals axioms (quarantined).  *)
(* ================================================================= *)
