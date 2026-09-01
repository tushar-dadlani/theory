(* ================================================================= *)
(*  MoreZeros.v  --  five more sign certificates, all from CheapSign. *)
(*                                                                    *)
(*  Each point is the same three blocks: an inlined vm_compute, a      *)
(*  tail_le discharge, and five side conditions.  Only M, r, Bq, the   *)
(*  theta term count and the threshold change -- all sized from the    *)
(*  measured margin |Z(t)| at that point.                             *)
(*                                                                    *)
(*    t      |Z|     M     r      Bq       theta N   Z interval        *)
(*    35    2.83    40    1/6    9/10        400   [ 1.577,  4.221]    *)
(*    39    1.79    60    1/7   13/20        500   [-2.554, -1.074]    *)
(*    42    1.10    90    1/9     2/5        550   [ 0.561,  1.691]    *)
(*    45    3.26    50    1/7       1        600   [-4.876, -1.770]    *)
(*    49    0.70   150   1/12     1/4        700   [ 0.368,  1.055]    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith ZArith.
Require Import ComplexField Cmodulus CoherenceSingularity IntervalArith
        IntervalAtan XirSignZ ThetaEnclose ZetaEM ZetaEnclose ZSign
        CheapSign FirstZeroBridge.
Open Scope R_scope.

Lemma chk35 :
  (match Izeta2 80 28 60 40 60 8 5 8 (35 # 1) 40 (9 # 10) with
   | Some (zr, zi) =>
       match IZ 60 8 5 (Itheta 40 4 4 (35 # 1) 400) zr zi with
       | Some i => Qle_bool (1 # 1) (ilo i)
       | None => false
       end
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem xir_35_neg : xir 35 < 0.
Proof.
  assert (Ht : Q2R (35 # 1) = 35) by (unfold Q2R; simpl; field).
  assert (Ethr : Q2R (1 # 1) = 1 / 1) by (unfold Q2R; simpl; field).
  assert (Eb : Q2R (9 # 10) = 9 / 10) by (unfold Q2R; simpl; field).
  assert (EI : INR (S 40) = 41)
    by (rewrite (INR_lit (S 40) 41%Z) by (vm_compute; reflexivity); reflexivity).
  rewrite <- Ht.
  apply (xir_neg_cheap 80 28 60 40 60 8 5 8 (35 # 1) 40 (9 # 10) 40 4 4 400 (1 # 1)).
  - rewrite Ht; lra.
  - rewrite Ethr; lra.
  - lia.
  - rewrite Eb, Ht.
    eapply Rle_trans; [ apply (tail_le 35 40 (1 / 6)) | ].
    + lra.
    + lra.
    + rewrite EI; lra.
    + rewrite EI; lra.
  - exact chk35.
Qed.

Lemma chk39 :
  (match Izeta2 80 28 60 40 60 8 5 8 (39 # 1) 60 (13 # 20) with
   | Some (zr, zi) =>
       match IZ 60 8 5 (Itheta 40 4 4 (39 # 1) 500) zr zi with
       | Some i => Qle_bool (ihi i) (Qopp (1 # 1))
       | None => false
       end
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem xir_39_pos : 0 < xir 39.
Proof.
  assert (Ht : Q2R (39 # 1) = 39) by (unfold Q2R; simpl; field).
  assert (Ethr : Q2R (1 # 1) = 1 / 1) by (unfold Q2R; simpl; field).
  assert (Eb : Q2R (13 # 20) = 13 / 20) by (unfold Q2R; simpl; field).
  assert (EI : INR (S 60) = 61)
    by (rewrite (INR_lit (S 60) 61%Z) by (vm_compute; reflexivity); reflexivity).
  rewrite <- Ht.
  apply (xir_pos_cheap 80 28 60 40 60 8 5 8 (39 # 1) 60 (13 # 20) 40 4 4 500 (1 # 1)).
  - rewrite Ht; lra.
  - rewrite Ethr; lra.
  - lia.
  - rewrite Eb, Ht.
    eapply Rle_trans; [ apply (tail_le 39 60 (1 / 7)) | ].
    + lra.
    + lra.
    + rewrite EI; lra.
    + rewrite EI; lra.
  - exact chk39.
Qed.

Lemma chk42 :
  (match Izeta2 80 28 60 40 60 8 5 8 (42 # 1) 90 (2 # 5) with
   | Some (zr, zi) =>
       match IZ 60 8 5 (Itheta 40 4 4 (42 # 1) 550) zr zi with
       | Some i => Qle_bool (1 # 2) (ilo i)
       | None => false
       end
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem xir_42_neg : xir 42 < 0.
Proof.
  assert (Ht : Q2R (42 # 1) = 42) by (unfold Q2R; simpl; field).
  assert (Ethr : Q2R (1 # 2) = 1 / 2) by (unfold Q2R; simpl; field).
  assert (Eb : Q2R (2 # 5) = 2 / 5) by (unfold Q2R; simpl; field).
  assert (EI : INR (S 90) = 91)
    by (rewrite (INR_lit (S 90) 91%Z) by (vm_compute; reflexivity); reflexivity).
  rewrite <- Ht.
  apply (xir_neg_cheap 80 28 60 40 60 8 5 8 (42 # 1) 90 (2 # 5) 40 4 4 550 (1 # 2)).
  - rewrite Ht; lra.
  - rewrite Ethr; lra.
  - lia.
  - rewrite Eb, Ht.
    eapply Rle_trans; [ apply (tail_le 42 90 (1 / 9)) | ].
    + lra.
    + lra.
    + rewrite EI; lra.
    + rewrite EI; lra.
  - exact chk42.
Qed.

Lemma chk45 :
  (match Izeta2 80 28 60 40 60 8 5 8 (45 # 1) 50 (1 # 1) with
   | Some (zr, zi) =>
       match IZ 60 8 5 (Itheta 40 4 4 (45 # 1) 600) zr zi with
       | Some i => Qle_bool (ihi i) (Qopp (3 # 2))
       | None => false
       end
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem xir_45_pos : 0 < xir 45.
Proof.
  assert (Ht : Q2R (45 # 1) = 45) by (unfold Q2R; simpl; field).
  assert (Ethr : Q2R (3 # 2) = 3 / 2) by (unfold Q2R; simpl; field).
  assert (Eb : Q2R (1 # 1) = 1 / 1) by (unfold Q2R; simpl; field).
  assert (EI : INR (S 50) = 51)
    by (rewrite (INR_lit (S 50) 51%Z) by (vm_compute; reflexivity); reflexivity).
  rewrite <- Ht.
  apply (xir_pos_cheap 80 28 60 40 60 8 5 8 (45 # 1) 50 (1 # 1) 40 4 4 600 (3 # 2)).
  - rewrite Ht; lra.
  - rewrite Ethr; lra.
  - lia.
  - rewrite Eb, Ht.
    eapply Rle_trans; [ apply (tail_le 45 50 (1 / 7)) | ].
    + lra.
    + lra.
    + rewrite EI; lra.
    + rewrite EI; lra.
  - exact chk45.
Qed.

Lemma chk49 :
  (match Izeta2 80 28 60 40 60 8 5 8 (49 # 1) 150 (1 # 4) with
   | Some (zr, zi) =>
       match IZ 60 8 5 (Itheta 40 4 4 (49 # 1) 700) zr zi with
       | Some i => Qle_bool (3 # 10) (ilo i)
       | None => false
       end
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem xir_49_neg : xir 49 < 0.
Proof.
  assert (Ht : Q2R (49 # 1) = 49) by (unfold Q2R; simpl; field).
  assert (Ethr : Q2R (3 # 10) = 3 / 10) by (unfold Q2R; simpl; field).
  assert (Eb : Q2R (1 # 4) = 1 / 4) by (unfold Q2R; simpl; field).
  assert (EI : INR (S 150) = 151)
    by (rewrite (INR_lit (S 150) 151%Z) by (vm_compute; reflexivity); reflexivity).
  rewrite <- Ht.
  apply (xir_neg_cheap 80 28 60 40 60 8 5 8 (49 # 1) 150 (1 # 4) 40 4 4 700 (3 # 10)).
  - rewrite Ht; lra.
  - rewrite Ethr; lra.
  - lia.
  - rewrite Eb, Ht.
    eapply Rle_trans; [ apply (tail_le 49 150 (1 / 12)) | ].
    + lra.
    + lra.
    + rewrite EI; lra.
    + rewrite EI; lra.
  - exact chk49.
Qed.
