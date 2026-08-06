(* ================================================================= *)
(*  LimInf.v  —  the liminf mirror of LimSup, via the -u duality.      *)
(*                                                                    *)
(*    is_liminf u L :=                                                 *)
(*      (forall eps>0, eventually  L - eps < u n)                      *)
(*      /\ (forall eps>0, infinitely often  u n < L + eps).            *)
(*                                                                    *)
(*  Everything follows from LimSup by  is_liminf u L <-> is_limsup     *)
(*  (-u) (-L)  (is_liminf_opp):                                        *)
(*    liminf_exists    : bounded u  ->  { L | is_liminf u L }          *)
(*    is_liminf_unique : is_liminf u L1 -> is_liminf u L2 -> L1 = L2   *)
(*    is_liminf_ge_lb  : (forall n, C <= u n) -> C <= L                *)
(*                                                                    *)
(*  Needed for the CORRECT Selberg endgame: the signed extremes        *)
(*  V = limsup Vsig, v = liminf Vsig satisfy V = -v = alpha, which the  *)
(*  degree-1 avg_below route cannot see.  Same classical-Reals axioms. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith.
Require Import LimSup.
Open Scope R_scope.

Definition is_liminf (u : nat -> R) (L : R) : Prop :=
  (forall eps, 0 < eps -> exists N0, forall n, (N0 <= n)%nat -> L - eps < u n)
  /\ (forall eps, 0 < eps -> forall N, exists k, (N <= k)%nat /\ u k < L + eps).

(* the duality with limsup of the negated sequence *)
Lemma is_liminf_opp : forall u L, is_liminf u L <-> is_limsup (fun n => - u n) (- L).
Proof.
  intros u L; split.
  - intros [Ha Hb]; split.
    + intros eps Heps; destruct (Ha eps Heps) as [N0 HN0]; exists N0; intros n Hn.
      specialize (HN0 n Hn); lra.
    + intros eps Heps N; destruct (Hb eps Heps N) as [k [Hk Hlt]];
        exists k; split; [ exact Hk | lra ].
  - intros [Ha Hb]; split.
    + intros eps Heps; destruct (Ha eps Heps) as [N0 HN0]; exists N0; intros n Hn.
      specialize (HN0 n Hn); lra.
    + intros eps Heps N; destruct (Hb eps Heps N) as [k [Hk Hlt]];
        exists k; split; [ exact Hk | lra ].
Qed.

Lemma is_liminf_unique : forall u L1 L2,
  is_liminf u L1 -> is_liminf u L2 -> L1 = L2.
Proof.
  intros u L1 L2 H1 H2; apply is_liminf_opp in H1, H2.
  pose proof (is_limsup_unique (fun n => - u n) (- L1) (- L2) H1 H2); lra.
Qed.

Lemma is_liminf_ge_lb : forall u L C,
  is_liminf u L -> (forall n, C <= u n) -> C <= L.
Proof.
  intros u L C H HC; apply is_liminf_opp in H.
  pose proof (is_limsup_le_ub (fun n => - u n) (- L) (- C) H
                (fun n => Ropp_le_contravar _ _ (HC n))); lra.
Qed.

Lemma is_liminf_le_ub_seq : forall u L C,
  is_liminf u L -> (forall n, u n <= C) -> L <= C.
Proof.
  intros u L C [Ha _] Hub.
  destruct (Rle_or_lt L C) as [H | H]; [ exact H | exfalso ].
  destruct (Ha ((L - C) / 2) ltac:(lra)) as [N0 HN0].
  specialize (HN0 N0 (le_n N0)); pose proof (Hub N0); lra.
Qed.

Theorem liminf_exists : forall u,
  (exists m, forall n, m <= u n) -> (exists M, forall n, u n <= M) ->
  { L | is_liminf u L }.
Proof.
  intros u Hlb Hub.
  assert (Hlb' : exists m, forall n, m <= - u n)
    by (destruct Hub as [M HM]; exists (- M); intros n; specialize (HM n); lra).
  assert (Hub' : exists M, forall n, - u n <= M)
    by (destruct Hlb as [m Hm]; exists (- m); intros n; specialize (Hm n); lra).
  destruct (limsup_exists (fun n => - u n) Hlb' Hub') as [L' HL'].
  exists (- L'); apply (proj2 (is_liminf_opp u (- L')));
    rewrite Ropp_involutive; exact HL'.
Qed.

Print Assumptions liminf_exists.

(* ================================================================= *)
(*  END LimInf.v  —  the liminf interface via the -u duality.          *)
(* ================================================================= *)
