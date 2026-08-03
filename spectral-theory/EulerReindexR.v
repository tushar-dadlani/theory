(* ================================================================= *)
(*  EulerReindexR.v                                                   *)
(*                                                                    *)
(*  THE R DISTRIBUTIVE REINDEX for general real exponent s.           *)
(*                                                                    *)
(*  The s = 2 Euler product (EulerProductZeta) reindexes the finite    *)
(*  primon-gas partition function through a Q model (PrimonGas over Q, *)
(*  transported by Q2R).  At a general real s the fugacity             *)
(*  p^{-s} = exp(-s ln p) is transcendental, so there is NO rational   *)
(*  model.  Here we re-derive the distributive law DIRECTLY over R:    *)
(*                                                                    *)
(*    R_euler_prod : sum over occupation states of the R Boltzmann     *)
(*      weight = product over modes of the truncated geometric sums    *)
(*      (a verbatim transcription of PrimonGas.euler_product to R);    *)
(*                                                                    *)
(*    Rweight_code : the R Boltzmann weight of an occupation vector    *)
(*      with fugacities p^{-s} IS (code ps ks)^{-s}  (the analytic     *)
(*      atom: Rpower / IZR-power algebra, primes positive);            *)
(*                                                                    *)
(*    euler_partial_reindex_Rs : hence the finite Euler partial        *)
(*      product Zpartial (map (p |-> p^{-s}) ps) N equals the sum of   *)
(*      the operator symbol z s over the coded numbers m = code ps ks. *)
(*                                                                    *)
(*  This is the general-s replacement for EulerProductZetaBound's      *)
(*  euler_partial_reindex_R.  The occupation-state index set is kept   *)
(*  as gstates (map fug ps) (S N) so the downstream distinctness /     *)
(*  positivity lemmas (codes_nat_nodup, codes_nat_pos, gstates ...)    *)
(*  reuse verbatim.                                                    *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via Rpower / z).     *)
(* ================================================================= *)

Require Import PrimonGas PrimeFactorizationN EulerReindex EulerProductR
        EulerProductZetaBound RecipSquareBound CZetaTerm2 Ell2Zeta.
From Stdlib Require Import QArith ZArith Znumtheory Reals Rpower Lra Lia List Arith.
Import ListNotations.
Open Scope R_scope.

(* ================================================================= *)
(*  1.  THE R BOLTZMANN WEIGHT AND THE Rlsum HELPERS                  *)
(* ================================================================= *)

(* Boltzmann weight over R: prod_i x_i^{k_i}  (mirror of PrimonGas.weight) *)
Fixpoint Rweight (xs : list R) (ks : list nat) : R :=
  match xs, ks with
  | x :: xs', k :: ks' => x ^ k * Rweight xs' ks'
  | _, _ => 1
  end.

Lemma Rlsum_map_scale_l : forall (A : Type) (c : R) (f : A -> R) (l : list A),
  Rlsum (map (fun a => c * f a) l) = c * Rlsum (map f l).
Proof.
  intros A c f; induction l as [|a l IH]; [ unfold Rlsum; simpl; ring | ].
  cbn [map]; rewrite !Rlsum_cons, IH; ring.
Qed.

Lemma Rlsum_map_scale_r : forall (A : Type) (c : R) (f : A -> R) (l : list A),
  Rlsum (map (fun a => f a * c) l) = Rlsum (map f l) * c.
Proof.
  intros A c f; induction l as [|a l IH]; [ unfold Rlsum; simpl; ring | ].
  cbn [map]; rewrite !Rlsum_cons, IH; ring.
Qed.

Lemma Rlsum_map_ext : forall (A : Type) (f g : A -> R) (l : list A),
  (forall a, f a = g a) -> Rlsum (map f l) = Rlsum (map g l).
Proof.
  intros A f g l H; induction l as [|a l IH]; [ reflexivity | ].
  cbn [map]; rewrite !Rlsum_cons, H, IH; reflexivity.
Qed.

Lemma Rlsum_map_flat_map :
  forall (A B : Type) (g : B -> R) (h : A -> list B) (L : list A),
    Rlsum (map g (flat_map h L))
    = Rlsum (map (fun a => Rlsum (map g (h a))) L).
Proof.
  intros A B g h; induction L as [|a L IH]; [ reflexivity | ].
  cbn [flat_map map]; rewrite map_app, Rlsum_app, Rlsum_cons, IH; reflexivity.
Qed.

(* the inner distributive step: fixing mode 0 at occupation k factors  *)
(* out x^k and leaves the sub-gas partition function (mirror of        *)
(* PrimonGas.inner_factor)                                             *)
Lemma Rinner_factor : forall x xs' k (L : list (list nat)),
  Rlsum (map (Rweight (x :: xs')) (map (cons k) L))
  = x ^ k * Rlsum (map (Rweight xs') L).
Proof.
  intros x xs' k L; rewrite map_map.
  rewrite <- (Rlsum_map_scale_l (list nat) (x ^ k) (Rweight xs') L).
  apply Rlsum_map_ext; intro ks; cbn [Rweight]; reflexivity.
Qed.

(* ================================================================= *)
(*  2.  THE R EULER PRODUCT (distributive law, over R)               *)
(* ================================================================= *)

(* The occupation-state carrier gstates qs K only depends on length qs, *)
(* so we index by the Q list qs (to reuse the s=2 distinctness lemmas)  *)
(* while the fugacities live in the parallel real list xrs.             *)
Theorem R_euler_prod : forall (xrs : list R) (qs : list Q) K,
  length xrs = length qs ->
  Rlsum (map (Rweight xrs) (gstates qs K))
  = fold_right Rmult 1 (map (fun x => Rlsum (map (fun k => x ^ k) (seq 0 K))) xrs).
Proof.
  induction xrs as [|x xrs' IH]; intros qs K Hlen.
  - destruct qs; [ | simpl in Hlen; discriminate ].
    cbn [gstates map Rweight]; unfold Rlsum; simpl; ring.
  - destruct qs as [|q qs']; [ simpl in Hlen; discriminate | ].
    cbn [gstates].
    rewrite Rlsum_map_flat_map.
    rewrite (Rlsum_map_ext nat
               (fun k => Rlsum (map (Rweight (x :: xrs')) (map (cons k) (gstates qs' K))))
               (fun k => x ^ k * Rlsum (map (Rweight xrs') (gstates qs' K)))
               (seq 0 K)
               (fun k => Rinner_factor x xrs' k (gstates qs' K))).
    rewrite (Rlsum_map_scale_r nat
               (Rlsum (map (Rweight xrs') (gstates qs' K))) (fun k => x ^ k) (seq 0 K)).
    rewrite (IH qs' K ltac:(simpl in Hlen; lia)).
    cbn [map fold_right]; ring.
Qed.

(* ================================================================= *)
(*  3.  THE ANALYTIC ATOM: R weight of p^{-s} modes = (code)^{-s}     *)
(* ================================================================= *)

Lemma Rweight_code : forall s ps ks,
  Forall prime ps -> length ps = length ks ->
  Rweight (map (fun p => Rpower (IZR p) (- s)) ps) ks
  = Rpower (IZR (code ps ks)) (- s).
Proof.
  intros s ps; induction ps as [|p ps' IH]; intros ks Hpr Hlen.
  - destruct ks; [ | simpl in Hlen; discriminate ].
    cbn [code map Rweight].
    change (IZR 1) with 1%R.
    unfold Rpower; rewrite ln_1, Rmult_0_r, exp_0; reflexivity.
  - destruct ks as [|k ks']; [ simpl in Hlen; discriminate | ].
    inversion Hpr as [| ? ? Hp Hpr']; subst.
    assert (Hpp : (2 <= p)%Z) by (destruct Hp; lia).
    assert (Hp0 : (0 < IZR p)%R) by (apply IZR_lt; lia).
    assert (Hc0 : (0 < IZR (code ps' ks'))%R)
      by (apply IZR_lt; pose proof (code_pos ps' ks' Hpr'); lia).
    assert (Hpk0 : (0 < IZR (p ^ Z.of_nat k))%R)
      by (apply IZR_lt; pose proof (zpow_ge_1 p k ltac:(lia)); lia).
    cbn [map Rweight code].
    rewrite (IH ks' Hpr' ltac:(simpl in Hlen; lia)).
    rewrite mult_IZR.
    rewrite <- (Rpower_mult_distr (IZR (p ^ Z.of_nat k)) (IZR (code ps' ks')) (- s) Hpk0 Hc0).
    f_equal.
    (* (Rpower (IZR p) (-s)) ^ k = Rpower (IZR (p ^ Z.of_nat k)) (-s) *)
    rewrite <- pow_IZR.
    rewrite <- (Rpower_pow k (IZR p) Hp0).
    assert (Hx : (0 < Rpower (IZR p) (- s))%R) by (unfold Rpower; apply exp_pos).
    rewrite <- (Rpower_pow k (Rpower (IZR p) (- s)) Hx).
    rewrite !Rpower_mult.
    f_equal; ring.
Qed.

(* ================================================================= *)
(*  4.  z s (Z.to_nat c) = c^{-s}   (the operator symbol bridge)      *)
(* ================================================================= *)

Lemma z_Z2Nat : forall s c, (1 <= c)%Z -> z s (Z.to_nat c) = Rpower (IZR c) (- s).
Proof.
  intros s c Hc; unfold z.
  replace (Nat.eqb (Z.to_nat c) 0) with false.
  2:{ symmetry; apply Nat.eqb_neq; intro H.
      pose proof (Z2Nat.id c ltac:(lia)) as Hid; rewrite H in Hid; simpl in Hid; lia. }
  rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity.
Qed.

(* ================================================================= *)
(*  5.  THE REINDEX: finite Euler partial product = sum of z s over    *)
(*      the coded numbers                                             *)
(* ================================================================= *)

Theorem euler_partial_reindex_Rs : forall s ps N,
  Forall prime ps ->
  Zpartial (map (fun p => Rpower (IZR p) (- s)) ps) N
  = Rlsum (map (fun ks => z s (Z.to_nat (code ps ks)))
               (gstates (map fug ps) (S N))).
Proof.
  intros s ps N Hpr.
  (* rewrite the geometric partial sums as Rlsum over seq 0 (S N) *)
  assert (HZ : Zpartial (map (fun p => Rpower (IZR p) (- s)) ps) N
    = fold_right Rmult 1
        (map (fun x => Rlsum (map (fun k => x ^ k) (seq 0 (S N))))
             (map (fun p => Rpower (IZR p) (- s)) ps))).
  { unfold Zpartial; f_equal; apply map_ext; intro x; symmetry; apply Rlsum_seq_sumf. }
  rewrite HZ.
  (* fold back into the sum over occupation states via the R Euler product *)
  rewrite <- (R_euler_prod (map (fun p => Rpower (IZR p) (- s)) ps) (map fug ps) (S N))
    by (rewrite !length_map; reflexivity).
  (* rewrite each Boltzmann weight as z s of the coded number *)
  f_equal; apply map_ext_in; intros ks Hks.
  assert (Hlen : length ks = length ps).
  { rewrite <- (length_map fug ps).
    apply (gstates_length (map fug ps) (S N) ks Hks). }
  rewrite (Rweight_code s ps ks Hpr (eq_sym Hlen)).
  rewrite (z_Z2Nat s (code ps ks) (code_pos ps ks Hpr)); reflexivity.
Qed.

Print Assumptions euler_partial_reindex_Rs.

(* ================================================================= *)
(*  END EulerReindexR.v                                              *)
(*  The finite Euler partial product Zpartial (p |-> p^{-s}) reindexes  *)
(*  directly over R as a sum of the operator symbol z s over the        *)
(*  coded numbers code ps ks -- the general-s replacement for the Q     *)
(*  reindex, ready to squeeze against zeta_cont.                        *)
(* ================================================================= *)
