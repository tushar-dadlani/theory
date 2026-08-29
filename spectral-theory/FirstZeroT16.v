(* ================================================================= *)
(*  FirstZeroT16.v  --  xir 16 < 0                                          *)
(*                                                                    *)
(*  Cheap: the quadrature is FirstZeroChk16's vm_compute, in its own   *)
(*  .vo.  This file only turns that boolean into a sign, through       *)
(*  XirSignChange.xir_neg_of and XirConstants' numerals for the two    *)
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
(*  Budget at L = 13/8: truncation <= 6e-8 (ET_ub), Mfin_16 <= 194,     *)
(*  n = 1024 so quadrature <= 2.1e-6.  msum >= 0.00195375 against a     *)
(*  threshold 1/(2(1/4+256)) = 1/512.5 = 0.00195122.                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import IntervalArith IntervalGint CoherenceSingularity
        IntegrandLip CompositeQuad XirSignChange XirConstants
        FirstZeroBridge FirstZeroChk16.
Local Open Scope R_scope.

(* lia cannot see through a nat literal built by Init.Nat.of_num_uint *)
Lemma pos1024 : (0 < 1024)%nat.
Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

Lemma h16 : Q2R (13 # 8192) = 13 / 8 / INR 1024.
Proof.
  rewrite (INR_lit 1024 1024) by (vm_compute; reflexivity).
  unfold Q2R; simpl; lra.
Qed.

Lemma msum16_b : Q2R (195375 # 100000000)
                <= msum (gint 16) 0 (13 / 8 / INR 1024) 1024.
Proof.
  assert (Hh : 0 <= Q2R (13 # 8192)) by (unfold Q2R; simpl; lra).
  assert (Et : Q2R (16 # 1) = 16) by (unfold Q2R; simpl; lra).
  pose proof chk16 as H.
  destruct (Imsum 46 25 32 14 32 12 30 5 4 46 16 (13 # 8192) 1024)
    as [i |] eqn:E; [ | discriminate ].
  pose proof (Imsum_sound 46 25 32 14 32 12 30 5 4 46 16 (13 # 8192) 1024
                i Hh E) as HC.
  rewrite Et, h16 in HC. unfold Icontains in HC.
  destruct HC as [Hb _].
  eapply Rle_trans; [ apply Qle_R; exact H | exact Hb ].
Qed.

Theorem xir_16_neg : xir 16 < 0.
Proof.
  apply (xir_neg_of 16 (13 / 8) 1024 (61 / 10) (6 / 100000000)
           pos1024 ltac:(lra) Mfin_16 ET_ub (Q2R (195375 # 100000000)) msum16_b).
  - rewrite (INR_lit 1024 1024) by (vm_compute; reflexivity).
    assert (E2 : Q2R (195375 # 100000000) = 195375 / 100000000) by (unfold Q2R; simpl; lra).
    rewrite E2. lra.
  - lra.
Qed.

Print Assumptions xir_16_neg.
