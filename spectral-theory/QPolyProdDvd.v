(* ================================================================= *)
(*  QPolyProdDvd.v                                                   *)
(*                                                                    *)
(*  TOOLKIT for the cyclotomic product identity (brick 6b/7).       *)
(*                                                                    *)
(*   • qdiv_deg_zero: g∣r with deg r < deg g (g≠0) ⟹ r = 0          *)
(*        — this is what forces the division remainder R_n to vanish. *)
(*   • qcopr_mul / qcopr_qprod: coprimality is preserved by products  *)
(*        (via Bézout), so a factor coprime to each Φ_d is coprime to *)
(*        their product.                                             *)
(*   • qprod_dvd: pairwise-coprime factors each dividing M have their *)
(*        product dividing M.                                        *)
(*  AXIOM-FREE.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyDeg QPolyGcd QPolyCoeffPIT QPolyMul QPolyDeriv
        QPolyCoprime QPolyRoot QPolySqfree QPolyEmbed Cyclotomic QProd.
Open Scope Qc_scope.

(* ----------------------------------------------------------------- *)
(*  g ∣ r with deg r < deg g (g ≠ 0)  ⟹  r = 0                      *)
(* ----------------------------------------------------------------- *)
Theorem qdiv_deg_zero : forall g r, (1 <= qdeg g)%nat ->
  qdivides g r -> qdegle r (Nat.pred (qdeg g)) -> qnorm r = [].
Proof.
  intros g r Hg1 [q Hq] Hdeg.
  destruct (list_eq_dec Qc_eq_dec (qnorm r) []) as [Hr | Hr]; [ exact Hr | exfalso ].
  assert (Hgn : qnorm g <> []).
  { intro Hz; unfold qdeg in Hg1; rewrite Hz in Hg1; simpl in Hg1; lia. }
  assert (Hqn : qnorm q <> []).
  { intro Hz; apply Hr; apply qeval_zero_norm; intro x;
      rewrite Hq, (qeval_qnorm_nil q Hz x); ring. }
  assert (Hcoeff : forall i, qcoeff r i = qcoeff (qmul g q) i)
    by (apply qeval_ext_coeff; intro x; rewrite Hq, qeval_mul; reflexivity).
  assert (Hrtop : qcoeff r (qdeg g + qdeg q) <> 0)
    by (rewrite Hcoeff; apply qmul_lead_nz; assumption).
  assert (Hle : (qdeg g + qdeg q <= qdeg r)%nat).
  { destruct (le_gt_dec (qdeg g + qdeg q) (qdeg r)) as [Hle | Hgt]; [ exact Hle | ].
    exfalso; apply Hrtop; apply (qdegle_above r); exact Hgt. }
  pose proof (qdegle_qdeg r (Nat.pred (qdeg g)) Hdeg); lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  h ∣ [c] with c ≠ 0  ⟹  h is a nonzero constant                  *)
(* ----------------------------------------------------------------- *)
Lemma divides_const_copr : forall h c, c <> 0 -> qdivides h (qconst c) ->
  exists c0, c0 <> 0 /\ (forall x, qeval h x = c0).
Proof.
  intros h c Hc Hdvd.
  assert (Hdeg := divides_const_deg0 h c Hc Hdvd).
  assert (Hhn : qnorm h <> [])
    by (apply (qdivides_nonzero h (qconst c) Hdvd); rewrite qnorm_const_nz; [ discriminate | exact Hc ]).
  assert (Hd0 : qdeg h = 0%nat) by (pose proof (qdegle_qdeg h 0 Hdeg); lia).
  exists (qcoeff h 0); split.
  - pose proof (qlead_nonzero h Hhn) as Hln; unfold qlead in Hln; rewrite Hd0 in Hln; exact Hln.
  - intro x; apply (qeval_const_of_degle0 h Hdeg).
Qed.

(* ----------------------------------------------------------------- *)
(*  coprimality is preserved by products                            *)
(* ----------------------------------------------------------------- *)
Lemma qcopr_restrict : forall g A h, qcopr g A -> qdivides h g -> qcopr h A.
Proof.
  intros g A h Hcop Hhg d Hdh Hda.
  apply Hcop; [ apply (qdivides_trans d h g Hdh Hhg) | exact Hda ].
Qed.

Lemma qcopr_euclid : forall h A B, qcopr h A -> qdivides h (qmul A B) -> qdivides h B.
Proof.
  intros h A B Hcop [r Hr].
  destruct (coprime_bezout h A Hcop) as [u [v Huv]].
  exists (qadd (qmul u B) (qmul v r)); intro x.
  specialize (Huv x); specialize (Hr x); rewrite qeval_mul in Hr.
  rewrite qeval_add, !qeval_mul.
  transitivity (qeval B x * (qeval u x * qeval h x + qeval v x * qeval A x));
    [ rewrite Huv; ring | ].
  transitivity (qeval u x * qeval h x * qeval B x + qeval v x * (qeval A x * qeval B x));
    [ ring | ].
  rewrite Hr; ring.
Qed.

Theorem qcopr_mul : forall g A B, qcopr g A -> qcopr g B -> qcopr g (qmul A B).
Proof.
  intros g A B HA HB h Hhg Hhab.
  assert (HhA : qcopr h A) by (apply (qcopr_restrict g A h HA Hhg)).
  assert (HhB : qdivides h B) by (apply (qcopr_euclid h A B HhA Hhab)).
  apply (HB h Hhg HhB).
Qed.

Theorem qcopr_qprod : forall g l,
  (forall d, In d l -> qcopr g (emb (Phi d))) -> qcopr g (qprod l).
Proof.
  intros g l; induction l as [|a l IH]; intro H.
  - intros h Hhg Hh1.
    apply (divides_const_copr h 1 qc_one_neq_zero).
    destruct Hh1 as [r Hr]; exists r; intro x; rewrite qeval_const, <- (Hr x), qeval_qprod_nil; reflexivity.
  - assert (Hcop : qcopr g (qmul (emb (Phi a)) (qprod l))).
    { apply qcopr_mul; [ apply H; left; reflexivity | apply IH; intros d Hd; apply H; right; exact Hd ]. }
    intros h Hhg Hh; apply Hcop; [ exact Hhg | ].
    destruct Hh as [r Hr]; exists r; intro x; rewrite qeval_mul, <- qeval_qprod_cons; apply Hr.
Qed.

(* ----------------------------------------------------------------- *)
(*  pairwise-coprime factors each dividing M ⟹ product divides M    *)
(* ----------------------------------------------------------------- *)
Theorem qprod_dvd : forall l M,
  NoDup l ->
  (forall d, In d l -> qdivides (emb (Phi d)) M) ->
  (forall i j, In i l -> In j l -> i <> j -> qcopr (emb (Phi i)) (emb (Phi j))) ->
  qdivides (qprod l) M.
Proof.
  induction l as [|a l IH]; intros M Hnd Hdvd Hcop.
  - exists M; intro x; rewrite qeval_qprod_nil; ring.
  - inversion Hnd as [| ? ? Hna Hnd']; subst.
    assert (Hpl : qdivides (qprod l) M)
      by (apply IH; [ exact Hnd' | intros d Hd; apply Hdvd; right; exact Hd
                    | intros i j Hi Hj; apply Hcop; right; assumption ]).
    assert (Hcopr : qcopr (emb (Phi a)) (qprod l)).
    { apply qcopr_qprod; intros d Hd; apply Hcop; [ left; reflexivity | right; exact Hd | ].
      intro; subst; contradiction. }
    pose proof (qcopr_product_divides (emb (Phi a)) (qprod l) M Hcopr
                  (Hdvd a (or_introl eq_refl)) Hpl) as Hmul.
    destruct Hmul as [r Hr]; exists r; intro x; rewrite qeval_qprod_cons, <- qeval_mul; apply Hr.
Qed.

Print Assumptions qprod_dvd.

(* ================================================================= *)
(*  END QPolyProdDvd.v                                               *)
(*  divides+smaller-degree ⟹ zero; coprimality preserved by products;*)
(*  pairwise-coprime factors' product divides.  Closed under the      *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
