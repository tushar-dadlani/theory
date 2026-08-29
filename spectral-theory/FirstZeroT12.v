(* ================================================================= *)
(*  FirstZeroT12.v  --  0 < xir 12                                          *)
(*                                                                    *)
(*  Cheap: the quadrature is FirstZeroChk12's vm_compute, in its own   *)
(*  .vo.  This file only turns that boolean into a sign, through       *)
(*  XirSignChange.xir_pos_of and XirConstants' numerals for the two    *)
(*  transcendental error terms.                                        *)
(*                                                                    *)
(*  TWO tactics are forbidden here, both because they make the KERNEL  *)
(*  re-run the quadrature in its ordinary evaluator at Qed:            *)
(*    - simpl (or cbn) on the chk hypothesis: it forces the option;    *)
(*      destruct ... eqn: keeps it frozen and is what is used instead. *)
(*    - refine/apply of a lemma abstracting the option, e.g.           *)
(*      extract_ub: unifying ?o against `match ?o with ...` is         *)
(*      higher-order and Coq solves it in a way that needs conversion. *)
(*  Both were measured: unbounded vs 0.001 s.                          *)
(*                                                                    *)
(*  Budget at L = 13/8: truncation <= 6e-8 (ET_ub), Mfin_12 <= 149,     *)
(*  n = 256 so quadrature <= 2.4e-5.  msum <= 0.003406 against a     *)
(*  threshold 1/(2(1/4+144)) = 1/288.5 = 0.00346620.                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import IntervalArith IntervalGint CoherenceSingularity
        IntegrandLip CompositeQuad XirSignChange XirConstants
        FirstZeroBridge FirstZeroChk12.
Local Open Scope R_scope.

(* lia cannot see through a nat literal built by Init.Nat.of_num_uint *)
Lemma pos256 : (0 < 256)%nat.
Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

Lemma h12 : Q2R (13 # 2048) = 13 / 8 / INR 256.
Proof.
  rewrite (INR_lit 256 256) by (vm_compute; reflexivity).
  unfold Q2R; simpl; lra.
Qed.

Lemma msum12_b : msum (gint 12) 0 (13 / 8 / INR 256) 256
                <= Q2R (3406 # 1000000).
Proof.
  assert (Hh : 0 <= Q2R (13 # 2048)) by (unfold Q2R; simpl; lra).
  assert (Et : Q2R (12 # 1) = 12) by (unfold Q2R; simpl; lra).
  pose proof chk12 as H.
  destruct (Imsum 46 25 32 14 32 12 30 5 4 46 12 (13 # 2048) 256)
    as [i |] eqn:E; [ | discriminate ].
  pose proof (Imsum_sound 46 25 32 14 32 12 30 5 4 46 12 (13 # 2048) 256
                i Hh E) as HC.
  rewrite Et, h12 in HC. unfold Icontains in HC.
  destruct HC as [_ Hb].
  eapply Rle_trans; [ exact Hb | apply Qle_R; exact H ].
Qed.

Theorem xir_12_pos : 0 < xir 12.
Proof.
  apply (xir_pos_of 12 (13 / 8) 256 (43 / 10) (6 / 100000000)
           pos256 ltac:(lra) Mfin_12 ET_ub (Q2R (3406 # 1000000)) msum12_b).
  - rewrite (INR_lit 256 256) by (vm_compute; reflexivity).
    assert (E2 : Q2R (3406 # 1000000) = 3406 / 1000000) by (unfold Q2R; simpl; lra).
    rewrite E2. lra.
  - lra.
Qed.

Print Assumptions xir_12_pos.
