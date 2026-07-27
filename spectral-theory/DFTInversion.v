(* ================================================================= *)
(*  DFTInversion.v                                                   *)
(*                                                                    *)
(*  THE COMPLEX DFT INVERSION THEOREM on the custom field C = R[i].   *)
(*                                                                    *)
(*  For a length-N signal f : nat -> C, with w N = exp(2 pi i / N) and *)
(*  its conjugate (= inverse) root wc N = conj(w N):                  *)
(*                                                                    *)
(*     (DFT f)  m  =  sum_{k<N}  f k * (wc N)^(m k)                    *)
(*     (IDFT g) k  =  (1/N) * sum_{m<N} g m * (w N)^(m k)             *)
(*                                                                    *)
(*     dft_inversion :  IDFT (DFT f) k = f k     (for k < N).         *)
(*                                                                    *)
(*  So the finite Fourier transform on C is INVERTIBLE (F^{-1} F = id) *)
(*  -- the capstone the roots-of-unity orthogonality was built for,    *)
(*  and the C analogue of WalshHadamard's H^2 = 8 I (= F^{-1}F=id      *)
(*  up to the 1/8).                                                   *)
(*                                                                    *)
(*  The engine is the two-index orthogonality (orthogonality_2):       *)
(*    sum_{m<N} (wc N)^(m l) (w N)^(m k) = N if k=l, else 0,           *)
(*  which for k<>l uses the INJECTIVITY of j |-> (w N)^j on {0..N-1}   *)
(*  (w_pow_inj, from primitivity).  The inversion is then finite       *)
(*  Fubini (Csum_swap) + scalar factoring + a delta-extraction         *)
(*  (Csum_delta), all pure C-field algebra.                          *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via C / trig).      *)
(* ================================================================= *)

From Stdlib Require Import Reals Arith Lia Lra List QArith Qcanon.
Import ListNotations.
(* The axiom-free algebraic DFT (added below, section RDFT) lives over the
   cyclotomic ring ℚ[x]/(Φ_N) from QPolyQuot; these bring in ζ, req, rpow,
   rsum and the Stage-2 orthogonality.  Imported BEFORE the ℂ layer so that
   ComplexField.C still wins, and R_scope is re-opened last for the ℂ code. *)
Require Import QPoly QPolyEmbed QPolyCoeffPIT QPolyQuot CycloOrthogonality.
Require Import ComplexField RootsOfUnity.   (* imported last: ComplexField.C wins over Reals' binomial C *)
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Ring lemmas for Cpow / Cconj                                     *)
(* ----------------------------------------------------------------- *)

Lemma Cpow_Cmul : forall x y n, Cpow (Cmul x y) n = Cmul (Cpow x n) (Cpow y n).
Proof. intros x y n; induction n as [|n IH]; cbn [Cpow]; [ ring | rewrite IH; ring ]. Qed.

Lemma Cconj_C1 : Cconj C1 = C1.
Proof. apply Ceq; simpl; ring. Qed.

Lemma Cconj_pow : forall a n, Cpow (Cconj a) n = Cconj (Cpow a n).
Proof.
  intros a n; induction n as [|n IH]; cbn [Cpow].
  - symmetry; apply Cconj_C1.
  - rewrite IH; symmetry; apply Cconj_mul.
Qed.

(* ----------------------------------------------------------------- *)
(*  The conjugate (= inverse) root and its properties                *)
(* ----------------------------------------------------------------- *)

Definition wc (N : nat) : C := Cconj (w N).

Lemma Cnorm2_w : forall N, Cnorm2 (w N) = 1.
Proof.
  intro N; unfold Cnorm2, w; cbn [Re Im].
  pose proof (sin2_cos2 (2 * PI / INR N)) as H; unfold Rsqr in H; lra.
Qed.

Lemma wc_w_1 : forall N, Cmul (wc N) (w N) = C1.
Proof.
  intro N; unfold wc.
  replace (Cmul (Cconj (w N)) (w N)) with (Cmul (w N) (Cconj (w N))) by ring.
  rewrite Cmul_conj, Cnorm2_w; reflexivity.
Qed.

Lemma wc_pow_N : forall N, (0 < N)%nat -> Cpow (wc N) N = C1.
Proof.
  intros N HN; unfold wc; rewrite Cconj_pow, (w_pow_N N HN); apply Cconj_C1.
Qed.

(* ----------------------------------------------------------------- *)
(*  Injectivity of  j |-> (w N)^j  on {0, ..., N-1}  (from primitivity) *)
(* ----------------------------------------------------------------- *)

Lemma w_pow_neq_of_lt : forall N a b, (a < b)%nat -> (b < N)%nat ->
  Cpow (w N) b <> Cpow (w N) a.
Proof.
  intros N a b Hab Hb Heq.
  apply (w_primitive N (b - a)); [ lia | ].
  assert (Hcancel : Cmul (Cpow (w N) a) (Cpow (wc N) a) = C1).
  { rewrite <- Cpow_Cmul.
    replace (Cmul (w N) (wc N)) with C1
      by (unfold wc; rewrite Cmul_conj, Cnorm2_w; reflexivity).
    apply Cpow_C1. }
  assert (Hexp : Cpow (w N) b = Cmul (Cpow (w N) (b - a)) (Cpow (w N) a))
    by (rewrite <- Cpow_add; f_equal; lia).
  assert (H1 : Cmul (Cmul (Cpow (w N) (b - a)) (Cpow (w N) a)) (Cpow (wc N) a)
             = Cmul (Cpow (w N) a) (Cpow (wc N) a))
    by (rewrite <- Hexp, Heq; reflexivity).
  replace (Cmul (Cmul (Cpow (w N) (b - a)) (Cpow (w N) a)) (Cpow (wc N) a))
    with (Cmul (Cpow (w N) (b - a)) (Cmul (Cpow (w N) a) (Cpow (wc N) a))) in H1 by ring.
  rewrite Hcancel in H1.
  replace (Cmul (Cpow (w N) (b - a)) C1) with (Cpow (w N) (b - a)) in H1 by ring.
  exact H1.
Qed.

Lemma w_pow_inj : forall N k l, (k < N)%nat -> (l < N)%nat ->
  Cpow (w N) k = Cpow (w N) l -> k = l.
Proof.
  intros N k l Hk Hl Heq.
  destruct (lt_eq_lt_dec k l) as [[H|H]|H].
  - exfalso; apply (w_pow_neq_of_lt N k l H Hl); symmetry; exact Heq.
  - exact H.
  - exfalso; apply (w_pow_neq_of_lt N l k H Hk); exact Heq.
Qed.

(* ----------------------------------------------------------------- *)
(*  Finite-sum plumbing over C                                       *)
(* ----------------------------------------------------------------- *)

Lemma Csum_zero : forall N, Csum (fun _ => C0) N = C0.
Proof. induction N as [|N IH]; cbn [Csum]; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma Csum_add : forall (g h : nat -> C) N,
  Csum (fun i => Cadd (g i) (h i)) N = Cadd (Csum g N) (Csum h N).
Proof. intros g h N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite IH; ring ]. Qed.

Lemma Csum_scale_l : forall c f N,
  Cmul c (Csum f N) = Csum (fun i => Cmul c (f i)) N.
Proof. intros c f N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite <- IH; ring ]. Qed.

Lemma Csum_scale_r : forall c f N,
  Cmul (Csum f N) c = Csum (fun i => Cmul (f i) c) N.
Proof. intros c f N; induction N as [|N IH]; cbn [Csum]; [ ring | rewrite <- IH; ring ]. Qed.

Lemma Csum_ext_bounded : forall (f g : nat -> C) N,
  (forall i, (i < N)%nat -> f i = g i) -> Csum f N = Csum g N.
Proof.
  intros f g N; induction N as [|N IH]; intro H; cbn [Csum]; [ reflexivity | ].
  rewrite IH by (intros i Hi; apply H; lia).
  rewrite (H N) by lia; reflexivity.
Qed.

(* finite Fubini: the double sum can be reordered *)
Lemma Csum_swap : forall (F : nat -> nat -> C) N M,
  Csum (fun m => Csum (fun l => F m l) M) N
  = Csum (fun l => Csum (fun m => F m l) N) M.
Proof.
  intros F N M; induction N as [|N IH].
  - rewrite (Csum_ext (fun l => Csum (fun m => F m l) 0) (fun _ => C0) M).
    + cbn [Csum]; symmetry; apply Csum_zero.
    + intro l; reflexivity.
  - cbn [Csum]; rewrite IH.
    rewrite <- (Csum_add (fun l => Csum (fun m => F m l) N) (fun l => F N l) M).
    apply Csum_ext; intro l; reflexivity.
Qed.

(* delta extraction: a sum whose l-th term is nonzero only at l=k *)
Lemma Csum_delta : forall (v : nat -> C) N k,
  Csum (fun l => if Nat.eqb k l then v l else C0) N
  = if Nat.ltb k N then v k else C0.
Proof.
  intros v N k; induction N as [|N IH].
  - cbn [Csum]; destruct (Nat.ltb_spec k 0); [ lia | reflexivity ].
  - cbn [Csum]; rewrite IH.
    destruct (Nat.ltb_spec k N); destruct (Nat.eqb_spec k N);
      destruct (Nat.ltb_spec k (S N)); try lia; try subst; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  TWO-INDEX ORTHOGONALITY  (the heart of inversion)                *)
(*     sum_{m<N} (wc N)^(m l) (w N)^(m k)  =  N [k=l]  or  0          *)
(* ----------------------------------------------------------------- *)

Lemma orthogonality_2 : forall N k l, (k < N)%nat -> (l < N)%nat ->
  Csum (fun m => Cmul (Cpow (wc N) (m * l)) (Cpow (w N) (m * k))) N
  = if Nat.eqb k l then RtoC (INR N) else C0.
Proof.
  intros N k l Hk Hl.
  assert (HN : (0 < N)%nat) by lia.
  (* rewrite each summand as a^m with a = (wc N)^l * (w N)^k *)
  rewrite (Csum_ext
    (fun m => Cmul (Cpow (wc N) (m * l)) (Cpow (w N) (m * k)))
    (fun m => Cpow (Cmul (Cpow (wc N) l) (Cpow (w N) k)) m) N).
  2:{ intro m.
      rewrite (Nat.mul_comm m l), (Nat.mul_comm m k), Cpow_mul, Cpow_mul.
      symmetry; apply Cpow_Cmul. }
  (* a^N = 1 *)
  assert (HaN : Cpow (Cmul (Cpow (wc N) l) (Cpow (w N) k)) N = C1).
  { rewrite Cpow_Cmul.
    replace (Cpow (Cpow (wc N) l) N) with C1.
    2:{ rewrite <- Cpow_mul, (Nat.mul_comm l N), Cpow_mul, (wc_pow_N N HN), Cpow_C1;
          reflexivity. }
    replace (Cpow (Cpow (w N) k) N) with C1.
    2:{ rewrite <- Cpow_mul, (Nat.mul_comm k N), Cpow_mul, (w_pow_N N HN), Cpow_C1;
          reflexivity. }
    ring. }
  destruct (Nat.eqb_spec k l) as [Hkl | Hkl].
  - (* k = l : a = 1, sum = N *)
    subst l.
    replace (Cmul (Cpow (wc N) k) (Cpow (w N) k)) with C1.
    2:{ rewrite <- Cpow_Cmul, wc_w_1, Cpow_C1; reflexivity. }
    apply sum_pow_eq_1; reflexivity.
  - (* k <> l : a <> 1 but a^N = 1, sum = 0 *)
    apply sum_pow_eq_0; [ | exact HaN ].
    intro Ha; apply Hkl.
    apply (w_pow_inj N k l Hk Hl).
    assert (Hwcw : Cmul (Cpow (wc N) l) (Cpow (w N) l) = C1).
    { rewrite <- Cpow_Cmul, wc_w_1, Cpow_C1; reflexivity. }
    assert (Hmul : Cmul (Cmul (Cpow (wc N) l) (Cpow (w N) k)) (Cpow (w N) l)
                 = Cpow (w N) l) by (rewrite Ha; ring).
    replace (Cmul (Cmul (Cpow (wc N) l) (Cpow (w N) k)) (Cpow (w N) l))
      with (Cmul (Cpow (w N) k) (Cmul (Cpow (wc N) l) (Cpow (w N) l))) in Hmul by ring.
    rewrite Hwcw in Hmul.
    replace (Cmul (Cpow (w N) k) C1) with (Cpow (w N) k) in Hmul by ring.
    exact Hmul.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE DFT, ITS INVERSE, AND THE INVERSION THEOREM                  *)
(* ----------------------------------------------------------------- *)

Definition DFT (N : nat) (f : nat -> C) (m : nat) : C :=
  Csum (fun k => Cmul (f k) (Cpow (wc N) (m * k))) N.

Definition IDFT (N : nat) (g : nat -> C) (k : nat) : C :=
  Cmul (Cinv (RtoC (INR N))) (Csum (fun m => Cmul (g m) (Cpow (w N) (m * k))) N).

Theorem dft_inversion : forall N f k, (0 < N)%nat -> (k < N)%nat ->
  IDFT N (DFT N f) k = f k.
Proof.
  intros N f k HN Hk.
  assert (HNc : RtoC (INR N) <> C0)
    by (intro Hc; exact (not_0_INR N ltac:(lia) (f_equal Re Hc))).
  unfold IDFT, DFT.
  (* move (w N)^(m k) inside the inner sum *)
  rewrite (Csum_ext
    (fun m => Cmul (Csum (fun l => Cmul (f l) (Cpow (wc N) (m * l))) N) (Cpow (w N) (m * k)))
    (fun m => Csum (fun l => Cmul (Cmul (f l) (Cpow (wc N) (m * l))) (Cpow (w N) (m * k))) N) N).
  2:{ intro m; apply Csum_scale_r. }
  (* finite Fubini: swap the m- and l-sums *)
  rewrite (Csum_swap
    (fun m l => Cmul (Cmul (f l) (Cpow (wc N) (m * l))) (Cpow (w N) (m * k))) N N).
  (* for each l<N, factor f l out and apply the two-index orthogonality *)
  rewrite (Csum_ext_bounded
    (fun l => Csum (fun m => Cmul (Cmul (f l) (Cpow (wc N) (m * l))) (Cpow (w N) (m * k))) N)
    (fun l => Cmul (f l) (if Nat.eqb k l then RtoC (INR N) else C0)) N).
  2:{ intros l Hl.
      rewrite (Csum_ext
        (fun m => Cmul (Cmul (f l) (Cpow (wc N) (m * l))) (Cpow (w N) (m * k)))
        (fun m => Cmul (f l) (Cmul (Cpow (wc N) (m * l)) (Cpow (w N) (m * k)))) N)
        by (intro m; ring).
      rewrite <- Csum_scale_l, (orthogonality_2 N k l Hk Hl); reflexivity. }
  (* push f l through the delta *)
  rewrite (Csum_ext_bounded
    (fun l => Cmul (f l) (if Nat.eqb k l then RtoC (INR N) else C0))
    (fun l => if Nat.eqb k l then Cmul (f l) (RtoC (INR N)) else C0) N).
  2:{ intros l _; destruct (Nat.eqb k l); [ reflexivity | ring ]. }
  (* extract the l=k term *)
  rewrite (Csum_delta (fun l => Cmul (f l) (RtoC (INR N))) N k).
  destruct (Nat.ltb_spec k N) as [_ | Hbad]; [ | lia ].
  (* (1/N) * (f k * N) = f k *)
  field; exact HNc.
Qed.

Print Assumptions dft_inversion.

(* ================================================================================= *)
(*  THE AXIOM-FREE ALGEBRAIC DFT, over R = ℚ[x]/(Φ_N) with the primitive root ζ.      *)
(*                                                                                    *)
(*  Same theorem — F^{-1}F = id — but with the transcendental root w = e^{2πi/N}      *)
(*  replaced by the algebraic ζ (QPolyQuot), so `Print Assumptions dft_inversion_R`   *)
(*  = Closed under the global context.  Built directly on `req` and the Stage-2       *)
(*  orthogonality `r_orthogonality`; the C proof above is the quarantined companion.  *)
(* ================================================================================= *)

Section RDFT.
  Variable Nn : nat.
  Hypothesis HN : (1 <= Nn)%nat.
  Local Open Scope Qc_scope.

  Notation Rq := (req Nn).

  (* ---- req-level finite-sum plumbing (the algebraic analogues of the Csum_* above) ---- *)
  Lemma rsum_zero : forall n, Rq (rsum (fun _ => []) n) [].
  Proof.
    induction n as [|n IH]; cbn [rsum].
    - apply req_refl.
    - apply (req_trans Nn _ (qadd [] []) _);
        [ apply req_qadd; [ exact IH | apply req_refl ]
        | apply req_of_qeval; intro x; rewrite qeval_add, !qeval_nil; ring ].
  Qed.

  Lemma rsum_add : forall g h n,
    Rq (rsum (fun i => qadd (g i) (h i)) n) (qadd (rsum g n) (rsum h n)).
  Proof.
    induction n as [|n IH]; cbn [rsum].
    - apply req_of_qeval; intro x; rewrite qeval_add, !qeval_nil; ring.
    - apply (req_trans Nn _ (qadd (qadd (rsum g n) (rsum h n)) (qadd (g n) (h n))) _).
      + apply req_qadd; [ exact IH | apply req_refl ].
      + apply req_of_qeval; intro x; rewrite !qeval_add; ring.
  Qed.

  Lemma rsum_scale_l : forall c f n, Rq (qmul c (rsum f n)) (rsum (fun i => qmul c (f i)) n).
  Proof.
    intros c f n; induction n as [|n IH]; cbn [rsum].
    - apply req_of_qeval; intro x; rewrite qeval_mul, !qeval_nil; ring.
    - apply (req_trans Nn _ (qadd (qmul c (rsum f n)) (qmul c (f n))) _).
      + apply req_of_qeval; intro x; rewrite qeval_mul, !qeval_add, !qeval_mul; ring.
      + apply req_qadd; [ exact IH | apply req_refl ].
  Qed.

  Lemma rsum_scale_r : forall c f n, Rq (qmul (rsum f n) c) (rsum (fun i => qmul (f i) c) n).
  Proof.
    intros c f n; induction n as [|n IH]; cbn [rsum].
    - apply req_of_qeval; intro x; rewrite qeval_mul, !qeval_nil; ring.
    - apply (req_trans Nn _ (qadd (qmul (rsum f n) c) (qmul (f n) c)) _).
      + apply req_of_qeval; intro x; rewrite qeval_mul, !qeval_add, !qeval_mul; ring.
      + apply req_qadd; [ exact IH | apply req_refl ].
  Qed.

  Lemma rsum_ext_bounded : forall f g n,
    (forall i, (i < n)%nat -> Rq (f i) (g i)) -> Rq (rsum f n) (rsum g n).
  Proof.
    intros f g n; induction n as [|n IH]; intro H; cbn [rsum].
    - apply req_refl.
    - apply req_qadd; [ apply IH; intros i Hi; apply H; lia | apply H; lia ].
  Qed.

  Lemma rsum_swap : forall (F : nat -> nat -> qpoly) n M,
    Rq (rsum (fun m => rsum (fun l => F m l) M) n)
       (rsum (fun l => rsum (fun m => F m l) n) M).
  Proof.
    intros F n M; induction n as [|n IH]; cbn [rsum].
    - apply req_sym, rsum_zero.
    - apply (req_trans Nn _
        (qadd (rsum (fun l => rsum (fun m => F m l) n) M) (rsum (fun l => F n l) M)) _).
      + apply req_qadd; [ exact IH | apply req_refl ].
      + apply req_sym, rsum_add.
  Qed.

  Lemma rsum_delta : forall (v : nat -> qpoly) n k,
    Rq (rsum (fun l => if (k =? l)%nat then v l else []) n)
       (if (k <? n)%nat then v k else []).
  Proof.
    intros v n k; induction n as [|n IH]; cbn [rsum].
    - apply req_refl.
    - apply (req_trans Nn _
        (qadd (if (k <? n)%nat then v k else []) (if (k =? n)%nat then v n else [])) _).
      + apply req_qadd; [ exact IH | apply req_refl ].
      + destruct (Nat.ltb_spec k n); destruct (Nat.eqb_spec k n);
          destruct (Nat.ltb_spec k (S n)); try lia; subst;
          apply req_of_qeval; intro x; rewrite qeval_add, ?qeval_nil; ring.
  Qed.

  (* ---- ζ periodicity and the generalized geometric orthogonality ---- *)
  Lemma zeta_pow_periodic : forall a t, Rq (rpow zeta (a + Nn * t)) (rpow zeta a).
  Proof.
    intros a t.
    apply (req_trans Nn _ (qmul (rpow zeta a) (rpow zeta (Nn * t))) _).
    - apply req_of_qeval; intro x; rewrite qeval_mul, !qeval_rpow_zeta, <- Qcpow_add; reflexivity.
    - apply (req_trans Nn _ (qmul (rpow zeta a) [1]) _).
      + apply req_qmul_l.
        apply (req_trans Nn _ (rpow (rpow zeta Nn) t) _).
        * apply req_of_qeval; intro x;
            rewrite (qeval_rpow (rpow zeta Nn) t), !qeval_rpow_zeta, <- Qcpow_mul; reflexivity.
        * apply (req_trans Nn _ (rpow [1] t) _).
          { apply req_rpow, zeta_pow_N; exact HN. }
          { apply req_of_qeval; intro x; rewrite qeval_rpow, !qeval_one, Qcpow_1_l; reflexivity. }
      + apply req_of_qeval; intro x; rewrite qeval_mul, qeval_one; ring.
  Qed.

  Lemma zeta_geom_sum : forall E,
    Rq (rsum (fun m => rpow zeta (m * E)) Nn)
       (if (E mod Nn =? 0)%nat then ofnatR Nn else []).
  Proof.
    intro E.
    apply (req_trans Nn _ (rsum (fun m => rpow zeta (m * (E mod Nn))) Nn) _).
    - apply rsum_ext_bounded; intros m _.
      replace (m * E)%nat with (m * (E mod Nn) + Nn * (m * (E / Nn)))%nat
        by (pose proof (Nat.div_mod_eq E Nn); nia).
      apply zeta_pow_periodic.
    - apply r_orthogonality; [ exact HN | apply Nat.mod_upper_bound; lia ].
  Qed.

  Lemma E_mod_iff : forall k l, (k < Nn)%nat -> (l < Nn)%nat ->
    (((Nn - 1) * l + k) mod Nn =? 0)%nat = (k =? l)%nat.
  Proof.
    intros k l Hk Hl.
    assert (HE : ((Nn - 1) * l + k + l = k + Nn * l)%nat) by (destruct Nn; [ lia | nia ]).
    destruct (Nat.eqb_spec k l) as [-> | Hkl].
    - replace ((Nn - 1) * l + l)%nat with (Nn * l)%nat by (destruct Nn; [ lia | nia ]).
      rewrite Nat.mul_comm, Nat.Div0.mod_mul; reflexivity.
    - apply Nat.eqb_neq; intro Hmod.
      apply Nat.Lcm0.mod_divide in Hmod; destruct Hmod as [c Hc].
      rewrite Hc in HE.
      (* HE : c*Nn + l = k + Nn*l ; take both sides mod Nn *)
      assert (Hll : (c * Nn + l) mod Nn = l)
        by (rewrite Nat.add_comm, Nat.Div0.mod_add; apply Nat.mod_small; exact Hl).
      assert (Hkk : (k + Nn * l) mod Nn = k)
        by (rewrite (Nat.mul_comm Nn l), Nat.Div0.mod_add; apply Nat.mod_small; exact Hk).
      rewrite HE, Hkk in Hll; exact (Hkl Hll).
  Qed.

  (* ---- the two-index orthogonality over R (analogue of orthogonality_2) ---- *)
  Lemma orthogonality_2_R : forall k l, (k < Nn)%nat -> (l < Nn)%nat ->
    Rq (rsum (fun m => qmul (rpow (rpow zeta (Nn - 1)) (m * l)) (rpow zeta (m * k))) Nn)
       (if (k =? l)%nat then ofnatR Nn else []).
  Proof.
    intros k l Hk Hl.
    apply (req_trans Nn _ (rsum (fun m => rpow zeta (m * ((Nn - 1) * l + k))) Nn) _).
    - apply rsum_ext_bounded; intros m _.
      apply req_of_qeval; intro x.
      rewrite qeval_mul, (qeval_rpow (rpow zeta (Nn - 1)) (m * l)), !qeval_rpow_zeta.
      rewrite <- !Qcpow_mul, <- Qcpow_add; f_equal; nia.
    - pose proof (zeta_geom_sum ((Nn - 1) * l + k)) as Hg.
      rewrite (E_mod_iff k l Hk Hl) in Hg; exact Hg.
  Qed.

  (* ---- the algebraic DFT, its inverse, and the inversion theorem ---- *)
  Definition wcz : qpoly := rpow zeta (Nn - 1).                 (* the inverse root ζ^{N-1} *)
  Definition invN : qpoly := qconst (/ qnat Nn).                (* the scalar 1/N in R *)

  Lemma invN_spec : Rq (qmul invN (ofnatR Nn)) [1].
  Proof.
    assert (Hnz : qnat Nn <> 0) by (destruct Nn; [ lia | apply qnat_Sk_nz ]).
    apply req_of_qeval; intro x.
    unfold invN, ofnatR; rewrite qeval_mul, !qeval_const, qeval_one.
    apply Qcmult_inv_l; exact Hnz.
  Qed.

  Definition DFT_R (f : nat -> qpoly) (m : nat) : qpoly :=
    rsum (fun k => qmul (f k) (rpow wcz (m * k))) Nn.
  Definition IDFT_R (g : nat -> qpoly) (k : nat) : qpoly :=
    qmul invN (rsum (fun m => qmul (g m) (rpow zeta (m * k))) Nn).

  Theorem dft_inversion_R : forall f k, (k < Nn)%nat -> Rq (IDFT_R (DFT_R f) k) (f k).
  Proof.
    intros f k Hk. unfold IDFT_R, DFT_R.
    apply (req_trans Nn _ (qmul invN (qmul (f k) (ofnatR Nn))) _).
    - apply req_qmul_l.
      (* move ζ^{mk} inside the inner sum *)
      apply (req_trans Nn _
        (rsum (fun m => rsum (fun l =>
           qmul (qmul (f l) (rpow wcz (m * l))) (rpow zeta (m * k))) Nn) Nn) _).
      { apply rsum_ext_bounded; intros m _; apply rsum_scale_r. }
      (* finite Fubini: swap the m- and l-sums *)
      apply (req_trans Nn _
        (rsum (fun l => rsum (fun m =>
           qmul (qmul (f l) (rpow wcz (m * l))) (rpow zeta (m * k))) Nn) Nn) _).
      { apply rsum_swap. }
      (* for each l<N, factor f_l out and apply the two-index orthogonality *)
      apply (req_trans Nn _
        (rsum (fun l => qmul (f l) (if (k =? l)%nat then ofnatR Nn else [])) Nn) _).
      { apply rsum_ext_bounded; intros l Hl.
        apply (req_trans Nn _
          (qmul (f l) (rsum (fun m => qmul (rpow wcz (m * l)) (rpow zeta (m * k))) Nn)) _).
        - apply (req_trans Nn _
            (rsum (fun m => qmul (f l) (qmul (rpow wcz (m * l)) (rpow zeta (m * k)))) Nn) _).
          + apply rsum_ext_bounded; intros m _; apply req_of_qeval; intro x; rewrite !qeval_mul; ring.
          + apply req_sym, rsum_scale_l.
        - apply req_qmul_l; unfold wcz; apply orthogonality_2_R; [ exact Hk | exact Hl ]. }
      (* push f_l through the delta *)
      apply (req_trans Nn _
        (rsum (fun l => if (k =? l)%nat then qmul (f l) (ofnatR Nn) else []) Nn) _).
      { apply rsum_ext_bounded; intros l _.
        destruct (k =? l)%nat;
          [ apply req_refl | apply req_of_qeval; intro x; rewrite qeval_mul, qeval_nil; ring ]. }
      (* extract the l=k term *)
      apply (req_trans Nn _ (if (k <? Nn)%nat then qmul (f k) (ofnatR Nn) else []) _).
      { apply rsum_delta. }
      destruct (Nat.ltb_spec k Nn); [ apply req_refl | lia ].
    - (* (1/N) · (f_k · N) ≡ f_k *)
      apply (req_trans Nn _ (qmul (f k) (qmul invN (ofnatR Nn))) _).
      + apply req_of_qeval; intro x; rewrite !qeval_mul; ring.
      + apply (req_trans Nn _ (qmul (f k) [1]) _).
        * apply req_qmul_l, invN_spec.
        * apply req_of_qeval; intro x; rewrite qeval_mul, qeval_one; ring.
  Qed.

End RDFT.

Print Assumptions dft_inversion_R.

(* ================================================================= *)
(*  END DFTInversion.v                                               *)
(*  The complex DFT on C = R[i] is invertible: IDFT (DFT f) k = f k.   *)
(*  Built from the two-index roots-of-unity orthogonality (which uses  *)
(*  primitivity => injectivity of j |-> (w N)^j) plus finite Fubini    *)
(*  and delta-extraction -- the F^{-1}F = id capstone of the finite    *)
(*  Fourier arc, the C analogue of WalshHadamard's H^2 = 8 I.          *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)
