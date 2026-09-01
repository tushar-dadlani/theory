(* ================================================================= *)
(*  NineZeros.v  --  nine zeros of Xi on the critical line.           *)
(*                                                                    *)
(*  ZeroCounting.alternation_zeros is the general machine: a monotone  *)
(*  sample sequence whose signs alternate (negative at even indices)   *)
(*  yields a zero in every gap.  Here it is fed the ten points         *)
(*                                                                    *)
(*    10, 16, 22, 26, 63/2, 35, 39, 42, 45, 49                        *)
(*                                                                    *)
(*  whose signs are +,-,+,-,+,-,+,-,+,- .  Index 0 is POSITIVE, so the *)
(*  sequence is fed starting at 16 (giving eight gaps) and the tenth   *)
(*  zero in (10,16) is added by hand.                                 *)
(*                                                                    *)
(*  The first three sign values came from Simpson quadrature (768,     *)
(*  512 and 1024 panels, hours of vm_compute).  The last six came      *)
(*  from CheapSign, one vm_compute each.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField RiemannXiEntire CoherenceSingularity
        BerryKeatingDilation ZeroCounting
        FirstZeroT10 FirstZeroT16 SecondZeroT22 ThirdZeroT26
        FourthZero MoreZeros.
Open Scope R_scope.

(* the sample sequence, starting at the first NEGATIVE value *)
Definition sq (i : nat) : R :=
  match i with
  | 0%nat => 16   | 1%nat => 22   | 2%nat => 26   | 3%nat => 63 / 2
  | 4%nat => 35   | 5%nat => 39   | 6%nat => 42   | 7%nat => 45
  | _ => 49
  end.

Lemma sq_mono : forall i, (i < 8)%nat -> sq i < sq (S i).
Proof.
  intros i Hi.
  do 8 (destruct i as [| i]; [ cbn [sq]; lra | ]).
  lia.
Qed.

Lemma sq_alt : forall i, (i <= 8)%nat -> alt_sign sq i.
Proof.
  intros i Hi. unfold alt_sign.
  do 9 (destruct i as [| i];
        [ cbn [sq Nat.even];
          first [ exact xir_16_neg | exact xir_22_pos | exact xir_26_neg
                | exact xir_315_pos | exact xir_35_neg | exact xir_39_pos
                | exact xir_42_neg | exact xir_45_pos | exact xir_49_neg ]
        | ]).
  lia.
Qed.

Theorem eight_zeros_in_gaps :
  forall i, (i < 8)%nat -> exists t, sq i < t < sq (S i) /\ spec Bxi t.
Proof. apply (alternation_zeros sq 8 sq_mono sq_alt). Qed.

(* the tenth sample point, below the sequence, gives one more gap *)
Theorem ninth_zero_in_10_16 : exists t, 10 < t < 16 /\ spec Bxi t.
Proof.
  apply sign_change_zero_down; [ lra | exact xir_10_pos | exact xir_16_neg ].
Qed.

Theorem nine_zeros :
  (exists t, 10 < t < 16 /\ spec Bxi t)
  /\ forall i, (i < 8)%nat -> exists t, sq i < t < sq (S i) /\ spec Bxi t.
Proof. split; [ exact ninth_zero_in_10_16 | exact eight_zeros_in_gaps ]. Qed.
