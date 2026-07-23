(* ================================================================= *)
(*  Parseval.v                                                       *)
(*                                                                    *)
(*  PARSEVAL / PLANCHEREL for the complex DFT on the custom field C.  *)
(*                                                                    *)
(*  The DFT is (up to the factor N) an ISOMETRY: it preserves the      *)
(*  Hermitian inner product.                                          *)
(*                                                                    *)
(*     plancherel : sum_{k<N} f k * conj(g k)                         *)
(*                    = (1/N) * sum_{m<N} (DFT f m) * conj(DFT g m)    *)
(*     parseval_norm : sum_{k<N} |f k|^2                              *)
(*                    = (1/N) * sum_{m<N} |DFT f m|^2                  *)
(*                                                                    *)
(*  With DFTInversion (F^{-1}F = id) and DFTConvolution (F diagonalises *)
(*  convolution), this completes the finite Fourier analysis on C.    *)
(*                                                                    *)
(*  Engine: the same two-index orthogonality (orthogonality_2) as      *)
(*  inversion, plus conjugation (conj commutes with the transform via  *)
(*  conj_wc_pow: conj((wc N)^j) = (w N)^j), finite Fubini and delta     *)
(*  extraction -- all C-field algebra.                               *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via C / trig).      *)
(* ================================================================= *)

From Stdlib Require Import Reals Arith Lia Lra.
Require Import ComplexField RootsOfUnity DFTInversion.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Conjugation commutes with the transform                          *)
(* ----------------------------------------------------------------- *)

Lemma conj_wc_pow : forall N j, Cconj (Cpow (wc N) j) = Cpow (w N) j.
Proof. intros N j; unfold wc; rewrite Cconj_pow, Cconj_involutive; reflexivity. Qed.

Lemma Csum_conj : forall f N, Cconj (Csum f N) = Csum (fun i => Cconj (f i)) N.
Proof.
  intros f N; induction N as [|N IH]; cbn [Csum].
  - apply Ceq; simpl; ring.
  - rewrite Cconj_add, IH; reflexivity.
Qed.

Lemma conj_DFT : forall N g m,
  Cconj (DFT N g m) = Csum (fun l => Cmul (Cconj (g l)) (Cpow (w N) (m * l))) N.
Proof.
  intros N g m; unfold DFT; rewrite Csum_conj.
  apply Csum_ext; intro l; rewrite Cconj_mul, conj_wc_pow; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  KEY LEMMA: the (wc)^{mk}-weighted sum of conj(DFT g) picks out      *)
(*  N * conj(g k)  (a "synthesis of the analysis")                    *)
(* ----------------------------------------------------------------- *)

Lemma sum_wc_conjDFT : forall N g k, (0 < N)%nat -> (k < N)%nat ->
  Csum (fun m => Cmul (Cpow (wc N) (m * k)) (Cconj (DFT N g m))) N
  = Cmul (RtoC (INR N)) (Cconj (g k)).
Proof.
  intros N g k HN Hk.
  rewrite (Csum_ext
    (fun m => Cmul (Cpow (wc N) (m * k)) (Cconj (DFT N g m)))
    (fun m => Csum (fun l => Cmul (Cconj (g l))
                     (Cmul (Cpow (wc N) (m * k)) (Cpow (w N) (m * l)))) N) N).
  2:{ intro m; rewrite conj_DFT, Csum_scale_l; apply Csum_ext; intro l; ring. }
  rewrite (Csum_swap
    (fun m l => Cmul (Cconj (g l)) (Cmul (Cpow (wc N) (m * k)) (Cpow (w N) (m * l)))) N N).
  rewrite (Csum_ext_bounded
    (fun l => Csum (fun m => Cmul (Cconj (g l))
                    (Cmul (Cpow (wc N) (m * k)) (Cpow (w N) (m * l)))) N)
    (fun l => Cmul (Cconj (g l)) (if Nat.eqb l k then RtoC (INR N) else C0)) N).
  2:{ intros l Hl; rewrite <- Csum_scale_l; f_equal.
      exact (orthogonality_2 N l k Hl Hk). }
  rewrite (Csum_ext
    (fun l => Cmul (Cconj (g l)) (if Nat.eqb l k then RtoC (INR N) else C0))
    (fun l => if Nat.eqb k l then Cmul (Cconj (g l)) (RtoC (INR N)) else C0) N).
  2:{ intro l; rewrite (Nat.eqb_sym l k); destruct (Nat.eqb k l); [ reflexivity | ring ]. }
  rewrite (Csum_delta (fun l => Cmul (Cconj (g l)) (RtoC (INR N))) N k).
  destruct (Nat.ltb_spec k N) as [_|Hbad]; [ | lia ].
  ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  PLANCHEREL (the N-scaled form, then the 1/N form)                *)
(* ----------------------------------------------------------------- *)

Lemma plancherel_N : forall N f g, (0 < N)%nat ->
  Cmul (RtoC (INR N)) (Csum (fun k => Cmul (f k) (Cconj (g k))) N)
  = Csum (fun m => Cmul (DFT N f m) (Cconj (DFT N g m))) N.
Proof.
  intros N f g HN.
  rewrite (Csum_ext
    (fun m => Cmul (DFT N f m) (Cconj (DFT N g m)))
    (fun m => Csum (fun k => Cmul (Cmul (f k) (Cpow (wc N) (m * k)))
                                  (Cconj (DFT N g m))) N) N).
  2:{ intro m; unfold DFT at 1; rewrite Csum_scale_r; reflexivity. }
  rewrite (Csum_swap
    (fun m k => Cmul (Cmul (f k) (Cpow (wc N) (m * k))) (Cconj (DFT N g m))) N N).
  rewrite (Csum_ext_bounded
    (fun k => Csum (fun m => Cmul (Cmul (f k) (Cpow (wc N) (m * k)))
                                  (Cconj (DFT N g m))) N)
    (fun k => Cmul (f k) (Cmul (RtoC (INR N)) (Cconj (g k)))) N).
  2:{ intros k Hk.
      rewrite (Csum_ext
        (fun m => Cmul (Cmul (f k) (Cpow (wc N) (m * k))) (Cconj (DFT N g m)))
        (fun m => Cmul (f k) (Cmul (Cpow (wc N) (m * k)) (Cconj (DFT N g m)))) N)
        by (intro m; ring).
      rewrite <- Csum_scale_l, (sum_wc_conjDFT N g k HN Hk); reflexivity. }
  rewrite Csum_scale_l; apply Csum_ext; intro k; ring.
Qed.

Theorem plancherel : forall N f g, (0 < N)%nat ->
  Csum (fun k => Cmul (f k) (Cconj (g k))) N
  = Cmul (Cinv (RtoC (INR N)))
         (Csum (fun m => Cmul (DFT N f m) (Cconj (DFT N g m))) N).
Proof.
  intros N f g HN.
  assert (HNc : RtoC (INR N) <> C0)
    by (intro Hc; exact (not_0_INR N ltac:(lia) (f_equal Re Hc))).
  rewrite <- (plancherel_N N f g HN); field; exact HNc.
Qed.

(* ----------------------------------------------------------------- *)
(*  PARSEVAL (g = f), in inner-product and in squared-modulus form    *)
(* ----------------------------------------------------------------- *)

Corollary parseval : forall N f, (0 < N)%nat ->
  Csum (fun k => Cmul (f k) (Cconj (f k))) N
  = Cmul (Cinv (RtoC (INR N)))
         (Csum (fun m => Cmul (DFT N f m) (Cconj (DFT N f m))) N).
Proof. intros N f HN; apply (plancherel N f f HN). Qed.

Corollary parseval_norm : forall N f, (0 < N)%nat ->
  Csum (fun k => RtoC (Cnorm2 (f k))) N
  = Cmul (Cinv (RtoC (INR N))) (Csum (fun m => RtoC (Cnorm2 (DFT N f m))) N).
Proof.
  intros N f HN.
  rewrite (Csum_ext (fun k => RtoC (Cnorm2 (f k)))
                    (fun k => Cmul (f k) (Cconj (f k))) N)
    by (intro k; symmetry; apply Cmul_conj).
  rewrite (Csum_ext (fun m => RtoC (Cnorm2 (DFT N f m)))
                    (fun m => Cmul (DFT N f m) (Cconj (DFT N f m))) N)
    by (intro m; symmetry; apply Cmul_conj).
  apply (parseval N f HN).
Qed.

Print Assumptions plancherel.
Print Assumptions parseval_norm.

(* ================================================================= *)
(*  END Parseval.v                                                   *)
(*  The complex DFT on C is (up to N) an isometry for the Hermitian    *)
(*  inner product: Plancherel  <f,g> = (1/N) <F f, F g>, and Parseval  *)
(*  ||f||^2 = (1/N) ||F f||^2.  With DFTInversion (F^{-1}F=id) and      *)
(*  DFTConvolution (diagonalises convolution) this completes the       *)
(*  finite Fourier analysis on the repo's own axiom-disciplined C.     *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)
