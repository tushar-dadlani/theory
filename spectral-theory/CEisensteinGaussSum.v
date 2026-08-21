(* ================================================================= *)
(*  CEisensteinGaussSum.v  —  the Gauss sum, and g^3 = p J.           *)
(*                                                                    *)
(*    gs  : the Gauss sum  sum_t chi(t) zeta^t                         *)
(*    gsb : the same with conjugated coefficients, g(chibar)           *)
(*    gauss_norm   : g . g(chibar) = p.delta_0 - N   (EXACT)           *)
(*    gauss_square : g . g       = J . g(chibar)     (EXACT)           *)
(*    gauss_cube   : g^3 = p J   in Z[om][zeta_p]                      *)
(*                                                                    *)
(*  THE GAUSS SUM IS THE CHARACTER.  In the group-ring model an        *)
(*  element is its coefficient function, and sum_t chi(t) zeta^t has   *)
(*  coefficient chi(u) at u -- so gs is literally chn p pi, with no    *)
(*  construction at all.  That is not a coincidence worth passing      *)
(*  over: it means the Esum toolkit built for norm_Jsum applies to     *)
(*  Gauss-sum products verbatim, and both identities below are the     *)
(*  same double-sum manoeuvre as brick 4 -- reindex the summation      *)
(*  index by i = n v, which is legitimate exactly when n <> 0.         *)
(*                                                                    *)
(*  BOTH IDENTITIES ARE EXACT, not merely congruences.  g . g(chibar)  *)
(*  is p.delta_0 - N on the nose, and g^2 is J . g(chibar) on the      *)
(*  nose; the quotient is needed once only, at the very end, to        *)
(*  discard the N.  Everything before that is equational, which is     *)
(*  why beq rather than ceq carries the two theorems.                  *)
(*                                                                    *)
(*  EVERY COEFFICIENT COMES FROM AN EARLIER BRICK.  The coefficient of *)
(*  g.g(chibar) away from 0 is sum_v chi(v) conj chi(1-v), which is    *)
(*  the DEGENERATE Jacobi sum of brick 3, equal to -1; at 0 it is      *)
(*  sum_v |chi(v)|^2 = p - 1.  The coefficient of g^2 at 0 is          *)
(*  sum_v chi(v)^2 = conj(sum_v chi(v)) = 0, which is brick 2; away    *)
(*  from 0 it is chi(n)^2 J, and chi(n)^2 = conj chi(n) on cube roots. *)
(*  So the whole file is those three facts, transported through one    *)
(*  reindexing each.                                                   *)
(*                                                                    *)
(*  gauss_cube IS STATED WITH Jsum, NOT WITH pi.  Nothing here needs   *)
(*  brick 6; substituting J = pi is a separate corollary, which keeps  *)
(*  this file independent of the hardest input it will eventually use. *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation Ring.
Require Import ZmodPStar CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinSum CEisensteinJacobi CEisensteinNormJ
        CycIndex CEisensteinCyc CEisensteinCycQuot.
Import ListNotations.
Open Scope Z_scope.

(* one scalar-pull lemma that E2 did not need *)
Lemma cscale_cmul_r : forall p, (1 <= p)%nat -> forall c f g,
  beq p (cmul p f (cscale c g)) (cscale c (cmul p f g)).
Proof.
  intros p Hp1 c f g n _. unfold cmul, cscale.
  rewrite <- (Esum_scale_l c (fun i => emul (f i) (g (msub p n i))) (seq 0 p)).
  apply Esum_ext. intros i _. ring.
Qed.

Section GaussSum.

Variable p : nat.
Variable pi : Eis.
Variable t0 : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdiv : Nat.divide 3 (p - 1)%nat.
Hypothesis Hn : enorm pi = Z.of_nat p.
Hypothesis Ht : edvd pi (esub (eZ t0) eom).

Notation ch := (chn p pi).
Notation P := (Z.of_nat p).

Lemma p_ge1 : (1 <= p)%nat. Proof. lia. Qed.

Definition gs : Cyc := chn p pi.
Definition gsb : Cyc := cbar gs.

(* ----------------------------------------------------------------- *)
(*  A.  small facts about the character                                *)
(* ----------------------------------------------------------------- *)
Lemma chn_norm1 : forall a, (1 <= a <= p - 1)%nat ->
  emul (ch a) (econj (ch a)) = eone.
Proof.
  intros a Ha. rewrite emul_econj.
  destruct (chn_cuberoot p pi Hp Hp7 Hn a Ha) as [E | [E | E]];
    rewrite E; reflexivity.
Qed.

Lemma chn_sq : forall a, (a < p)%nat -> emul (ch a) (ch a) = econj (ch a).
Proof.
  intros a Ha. destruct (Nat.eq_dec a 0) as [-> | Ha0].
  - rewrite (chn_zero p pi Hp Hn). reflexivity.
  - apply cuberoot_sq. apply (chn_cuberoot p pi Hp Hp7 Hn). lia.
Qed.

(* chi(-i) = chi(i), because chi(-1) = 1 *)
Lemma chn_neg : forall i, (i < p)%nat -> ch (msub p 0 i) = ch i.
Proof.
  intros i Hi.
  transitivity (ch (((p - 1) * i) mod p)%nat).
  - apply (cg_chn p pi t0 Hp Hp7 Hdiv Hn Ht).
    destruct (msub_cg p p_ge1 0 i ltac:(lia)) as [a Ha].
    destruct (cgp_mod p p_ge1 ((p - 1) * i)%nat) as [b Hb].
    rewrite Nat2Z.inj_mul in Hb.
    exists (a - b - Z.of_nat i).
    replace (Z.of_nat (p - 1)) with (P - 1) in Hb by lia.
    replace (Z.of_nat 0) with 0 in Ha by reflexivity. lia.
  - rewrite (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht (p - 1)%nat i).
    rewrite (chn_minus_one p pi t0 Hp Hp7 Hdiv Hn Ht). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the index identity behind the reindexing                       *)
(* ----------------------------------------------------------------- *)
Lemma msub_mulmod : forall n v, (n < p)%nat -> (v < p)%nat ->
  msub p n ((n * v) mod p)%nat = ((n * msub p 1 v) mod p)%nat.
Proof.
  intros n v Hn' Hv.
  apply (cgp_eq p p_ge1);
    [ apply msub_lt; exact p_ge1 | apply Nat.mod_upper_bound; lia | ].
  destruct (msub_cg p p_ge1 n ((n * v) mod p)%nat
              ltac:(pose proof (Nat.mod_upper_bound (n * v)%nat p ltac:(lia)); lia))
    as [a Ha].
  destruct (cgp_mod p p_ge1 (n * v)%nat) as [b Hb]. rewrite Nat2Z.inj_mul in Hb.
  destruct (cgp_mod p p_ge1 (n * msub p 1 v)%nat) as [c Hc].
  rewrite Nat2Z.inj_mul in Hc.
  destruct (msub_cg p p_ge1 1 v ltac:(lia)) as [d Hd].
  set (M := Z.of_nat ((n * v) mod p)%nat) in *.
  set (W := Z.of_nat (msub p 1 v)) in *.
  set (N := Z.of_nat n) in *. set (V := Z.of_nat v) in *.
  exists (a - b - N * d - c).
  assert (Q1 : Z.of_nat (msub p n ((n * v) mod p)%nat) = N - M + a * P) by lia.
  assert (Q2 : M = N * V + b * P) by lia.
  assert (Q3 : Z.of_nat ((n * msub p 1 v) mod p)%nat = N * W + c * P) by lia.
  assert (Q4 : W = 1 - V + d * P) by (replace (Z.of_nat 1) with 1 in Hd by reflexivity; lia).
  rewrite Q1, Q2, Q3, Q4. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the two Jacobi sums, over all of F_p                           *)
(* ----------------------------------------------------------------- *)
Lemma seq0p2 : seq 0 p = 0%nat :: 1%nat :: seq 2 (p - 2).
Proof.
  replace p with (S (S (p - 2))) at 1 by lia. cbn [seq]. repeat f_equal; lia.
Qed.

Lemma msub1_1 : msub p 1 1 = 0%nat.
Proof.
  unfold msub. replace (1 + p - 1)%nat with p by lia. apply Nat.Div0.mod_same.
Qed.

Lemma msub1_small : forall v, (2 <= v <= p - 1)%nat -> msub p 1 v = (1 + p - v)%nat.
Proof. intros v Hv. unfold msub. apply Nat.mod_small. lia. Qed.

Lemma jacobi_full :
  Esum (fun v => emul (ch v) (econj (ch (msub p 1 v)))) (seq 0 p) = eopp eone.
Proof.
  rewrite seq0p2, !Esum_cons.
  rewrite (chn_zero p pi Hp Hn), msub1_1, (chn_zero p pi Hp Hn), econj_zero.
  rewrite (Esum_ext _ (fun x => emul (ch x) (econj (ch (1 + p - x)%nat)))
             (seq 2 (p - 2))).
  - rewrite (jacobi_degenerate p pi t0 Hp Hp7 Hdiv Hn Ht). ring.
  - intros x Hx. apply in_seq in Hx. rewrite (msub1_small x ltac:(lia)). reflexivity.
Qed.

Lemma chisq_full : Esum (fun i => econj (ch i)) (seq 0 p) = ezero.
Proof.
  pose proof (char_sum_zero_full p pi t0 Hp Hp7 Hdiv Hn Ht) as H.
  apply (f_equal econj) in H.
  rewrite econj_Esum, econj_zero in H. exact H.
Qed.

Lemma Jsum_full :
  Esum (fun v => emul (ch v) (ch (msub p 1 v))) (seq 0 p) = Jsum p pi.
Proof.
  unfold Jsum. rewrite seq0p2, !Esum_cons.
  rewrite (chn_zero p pi Hp Hn), msub1_1, (chn_zero p pi Hp Hn).
  rewrite (Esum_ext _ (fun t => emul (ch t) (ch (1 + p - t)%nat)) (seq 2 (p - 2))).
  - ring.
  - intros x Hx. apply in_seq in Hx. rewrite (msub1_small x ltac:(lia)). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the two exact identities                                       *)
(* ----------------------------------------------------------------- *)
Theorem gauss_norm :
  beq p (cmul p gs gsb) (csub (cscale (eZ P) (cone p)) cN).
Proof.
  intros n Hn'. unfold cmul, gsb, cbar, gs, csub, cscale, cN, cone.
  destruct (Nat.eq_dec n 0) as [-> | Hn0].
  - (* the diagonal coefficient is p - 1 *)
    rewrite (Esum_ext _ (fun i => emul (ch i) (econj (ch i))) (seq 0 p)).
    2:{ intros i Hi. apply in_seq in Hi. rewrite (chn_neg i ltac:(lia)). reflexivity. }
    assert (Hs : seq 0 p = 0%nat :: seq 1 (p - 1))
      by (replace p with (S (p - 1)) at 1 by lia; reflexivity).
    rewrite Hs, Esum_cons, (chn_zero p pi Hp Hn).
    rewrite (Esum_ext _ (fun _ => eone) (seq 1 (p - 1))).
    2:{ intros i Hi. apply in_seq in Hi. apply chn_norm1. lia. }
    rewrite Esum_const_one, length_seq, (cdelta_hit p 0).
    assert (E : eZ (Z.of_nat (p - 1)) = esub (emul (eZ P) eone) eone).
    { assert (E1 : emul (eZ P) eone = eZ P) by ring.
      rewrite E1, <- eZ_one, <- eZ_sub. f_equal. lia. }
    rewrite E. ring.
  - (* off the diagonal it is the degenerate Jacobi sum, namely -1 *)
    assert (Hnd : ~ Nat.divide p n) by (apply unit_not_div; lia).
    rewrite <- (Esum_mulperm p p_ge1 Hp
                 (fun i => emul (ch i) (econj (ch (msub p n i)))) n Hnd).
    rewrite (Esum_ext _ (fun v => emul (ch v) (econj (ch (msub p 1 v)))) (seq 0 p)).
    2:{ intros v Hv. apply in_seq in Hv.
        rewrite (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht n v).
        rewrite (msub_mulmod n v ltac:(lia) ltac:(lia)).
        rewrite (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht n (msub p 1 v)).
        rewrite econj_mul.
        assert (E : emul (emul (ch n) (ch v))
                         (emul (econj (ch n)) (econj (ch (msub p 1 v))))
                    = emul (emul (ch n) (econj (ch n)))
                           (emul (ch v) (econj (ch (msub p 1 v))))) by ring.
        rewrite E, (chn_norm1 n ltac:(lia)). ring. }
    rewrite jacobi_full, (cdelta_miss p p_ge1 0 n ltac:(lia) ltac:(lia) Hn0).
    assert (E : emul (eZ P) ezero = ezero) by ring. rewrite E. ring.
Qed.

Theorem gauss_square :
  beq p (cmul p gs gs) (cscale (Jsum p pi) gsb).
Proof.
  intros n Hn'. unfold cmul, gsb, cbar, gs, cscale.
  destruct (Nat.eq_dec n 0) as [-> | Hn0].
  - (* the diagonal coefficient is sum_v chi(v)^2 = conj(sum_v chi(v)) = 0 *)
    rewrite (Esum_ext _ (fun i => econj (ch i)) (seq 0 p)).
    2:{ intros i Hi. apply in_seq in Hi.
        rewrite (chn_neg i ltac:(lia)). apply chn_sq. lia. }
    rewrite chisq_full, (chn_zero p pi Hp Hn), econj_zero. ring.
  - (* off the diagonal it is chi(n)^2 J = conj(chi(n)) J *)
    assert (Hnd : ~ Nat.divide p n) by (apply unit_not_div; lia).
    rewrite <- (Esum_mulperm p p_ge1 Hp
                 (fun i => emul (ch i) (ch (msub p n i))) n Hnd).
    rewrite (Esum_ext _ (fun v => emul (econj (ch n))
                                       (emul (ch v) (ch (msub p 1 v)))) (seq 0 p)).
    2:{ intros v Hv. apply in_seq in Hv.
        rewrite (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht n v).
        rewrite (msub_mulmod n v ltac:(lia) ltac:(lia)).
        rewrite (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht n (msub p 1 v)).
        assert (E : emul (emul (ch n) (ch v)) (emul (ch n) (ch (msub p 1 v)))
                    = emul (emul (ch n) (ch n))
                           (emul (ch v) (ch (msub p 1 v)))) by ring.
        rewrite E, (chn_sq n ltac:(lia)). reflexivity. }
    rewrite Esum_scale_l, Jsum_full. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the cube                                                       *)
(* ----------------------------------------------------------------- *)
Theorem gauss_cube :
  ceq p (cpow p gs 3) (cemb p (emul (eZ P) (Jsum p pi))).
Proof.
  (* g^3 = g . (g . g) *)
  assert (Hgg : beq p (cpow p gs 3) (cmul p gs (cmul p gs gs))).
  { cbn [cpow].
    exact (beq_cmul p p_ge1 gs gs (cmul p gs (cmul p gs (cone p))) (cmul p gs gs)
             (beq_refl p gs)
             (beq_cmul p p_ge1 gs gs (cmul p gs (cone p)) gs
                (beq_refl p gs) (cmul_1_r p p_ge1 gs))). }
  (* ... = g . (J . g(chibar)) = J . (g . g(chibar)) *)
  assert (H1 : beq p (cpow p gs 3) (cscale (Jsum p pi) (cmul p gs gsb))).
  { apply (beq_trans p _ (cmul p gs (cmul p gs gs))); [ exact Hgg | ].
    apply (beq_trans p _ (cmul p gs (cscale (Jsum p pi) gsb))).
    - exact (beq_cmul p p_ge1 gs gs (cmul p gs gs) (cscale (Jsum p pi) gsb)
               (beq_refl p gs) gauss_square).
    - exact (cscale_cmul_r p p_ge1 (Jsum p pi) gs gsb). }
  (* ... = J . (p.delta_0 - N) = p J . delta_0 - J . N *)
  assert (H2 : beq p (cscale (Jsum p pi) (cmul p gs gsb))
                     (csub (cemb p (emul (eZ P) (Jsum p pi)))
                           (cscale (Jsum p pi) cN))).
  { apply (beq_trans p _ (cscale (Jsum p pi)
             (csub (cscale (eZ P) (cone p)) cN))).
    - exact (beq_cscale p (Jsum p pi) (cmul p gs gsb)
               (csub (cscale (eZ P) (cone p)) cN) gauss_norm).
    - intros u _. unfold csub, cemb, cscale, cone, cN. ring. }
  (* and J . N is a constant, so it vanishes in the quotient *)
  assert (H3 : ceq p (csub (cemb p (emul (eZ P) (Jsum p pi)))
                           (cscale (Jsum p pi) cN))
                     (cemb p (emul (eZ P) (Jsum p pi)))).
  { intros u v _ _. unfold csub, cscale, cN. ring. }
  apply (ceq_trans p _ (cscale (Jsum p pi) (cmul p gs gsb)));
    [ exact (beq_ceq p _ _ H1) | ].
  apply (ceq_trans p _ (csub (cemb p (emul (eZ P) (Jsum p pi)))
                             (cscale (Jsum p pi) cN)));
    [ exact (beq_ceq p _ _ H2) | exact H3 ].
Qed.

End GaussSum.

Print Assumptions gauss_norm.
Print Assumptions gauss_square.
Print Assumptions gauss_cube.
