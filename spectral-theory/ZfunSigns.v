(* ================================================================= *)
(*  ZfunSigns.v  --  the four certified signs, restated for Z.        *)
(*                                                                    *)
(*  xir_sign_Z says xir t = -c(t) Z(t) with c(t) > 0, so every sign    *)
(*  already certified by quadrature transfers to Z with a flip.  The   *)
(*  alternation that located the three zeros reads, in Z:             *)
(*                                                                    *)
(*      Z(10) < 0,  Z(16) > 0,  Z(22) < 0,  Z(26) > 0.                *)
(*                                                                    *)
(*  This is a regression test as much as a restatement: the four xir   *)
(*  signs were obtained by four INDEPENDENT interval computations,     *)
(*  and xir_sign_Z was derived symbolically from the strip identity    *)
(*  with no reference to them.  A sign error in either would show up   *)
(*  here as a broken alternation.                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField CoherenceSingularity XirSignZ
        FirstZeroT10 FirstZeroT16 SecondZeroT22 ThirdZeroT26.
Open Scope R_scope.

Theorem Zfun_10_neg : Zfun 10 < 0.
Proof. apply (proj1 (xir_pos_iff_Z_neg 10)). exact xir_10_pos. Qed.

Theorem Zfun_16_pos : 0 < Zfun 16.
Proof. apply (proj1 (xir_neg_iff_Z_pos 16)). exact xir_16_neg. Qed.

Theorem Zfun_22_neg : Zfun 22 < 0.
Proof. apply (proj1 (xir_pos_iff_Z_neg 22)). exact xir_22_pos. Qed.

Theorem Zfun_26_pos : 0 < Zfun 26.
Proof. apply (proj1 (xir_neg_iff_Z_pos 26)). exact xir_26_neg. Qed.

(* the alternation, in one statement *)
Theorem Zfun_alternates :
  Zfun 10 < 0 /\ 0 < Zfun 16 /\ Zfun 22 < 0 /\ 0 < Zfun 26.
Proof.
  repeat split;
    [ exact Zfun_10_neg | exact Zfun_16_pos
    | exact Zfun_22_neg | exact Zfun_26_pos ].
Qed.
