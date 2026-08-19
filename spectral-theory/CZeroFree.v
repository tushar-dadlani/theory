(* ================================================================= *)
(*  CZeroFree.v  —  discharging HGne0: a MAXIMAL peel list leaves a     *)
(*  zero-free cofactor.                                                *)
(*                                                                    *)
(*    cofactor_zero_free : F pointwise-continuous and holomorphic on    *)
(*      Cmod z < R2, with 0 < Rr, Rr + 1 < R2, F C0 <> C0 and |F| <= M  *)
(*      on the circle |z| = Rr, yields l and G with                     *)
(*                                                                    *)
(*        F = prodfac l . G,  G regular on the disk,                    *)
(*        every zero in l of modulus < Rr/4,  and                       *)
(*        forall z, Cmod z < Rr/4 -> G z <> C0.        <-- HGne0        *)
(*                                                                    *)
(*  THE ARGUMENT.  CPeelBound.peel_length_bound says one N bounds the   *)
(*  length of EVERY peel list.  So the set of achievable lengths is a   *)
(*  bounded, inhabited set of naturals (inhabited by 0, via DivBy_nil)  *)
(*  and therefore has a GREATEST element.  Take a list realising it.    *)
(*  Its cofactor cannot vanish anywhere in the disk: a zero w there     *)
(*  could be peeled off by CZeroListFactor.DivBy_cons, producing a list *)
(*  of length one greater -- contradicting maximality.  That is exactly *)
(*  HGne0, and it never mentions isolation, accumulation, compactness   *)
(*  or the identity theorem.                                           *)
(*                                                                    *)
(*  The greatest-element step uses Classical_Prop.classic (already in   *)
(*  the axiom set) via a downward induction on the bound.  It does NOT  *)
(*  use choice: the maximum is a NATURAL NUMBER extracted from a        *)
(*  decidable-by-classic predicate, not a function chosen pointwise.    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Classical.
Require Import ComplexField Cmodulus Holomorphic CDeriv CPathIntegral
        JensenMultiZero CZeroFactorDisk CZeroListFactor CPeelBound.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A bounded, inhabited predicate on nat has a greatest element.      *)
(*  Downward induction on the bound; classic decides each level.       *)
(* ----------------------------------------------------------------- *)
Lemma bounded_has_max : forall (P : nat -> Prop) (N : nat),
  P 0%nat -> (forall n, P n -> (n <= N)%nat) ->
  exists m, P m /\ forall k, P k -> (k <= m)%nat.
Proof.
  intros P N. revert P. induction N as [| N IH]; intros P H0 Hbd.
  - exists 0%nat. split; [ exact H0 | ]. intros k Hk. exact (Hbd k Hk).
  - destruct (classic (P (S N))) as [Hyes | Hno].
    + exists (S N). split; [ exact Hyes | ]. intros k Hk. exact (Hbd k Hk).
    + apply (IH P H0). intros n Hn.
      assert (Hle : (n <= S N)%nat) by exact (Hbd n Hn).
      assert (Hne : n <> S N) by (intro E; apply Hno; rewrite <- E; exact Hn).
      lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  the achievable peel lengths                                        *)
(* ----------------------------------------------------------------- *)
Definition PeelLen (F : C -> C) (R2 Rr : R) (n : nat) : Prop :=
  exists (l : list C) (G : C -> C),
    (forall z, F z = Cmul (prodfac l z) (G z)) /\
    disk_holo G R2 /\ ptcont G /\
    (forall w, In w l -> Cmod w < Rr / 4) /\
    length l = n.

Theorem cofactor_zero_free : forall (F : C -> C) (R2 Rr M : R),
  0 < Rr -> Rr + 1 < R2 ->
  F C0 <> C0 ->
  ptcont F ->
  disk_holo F R2 ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  exists (l : list C) (G : C -> C),
    (forall z, F z = Cmul (prodfac l z) (G z)) /\
    disk_holo G R2 /\ ptcont G /\
    (forall w, In w l -> Cmod w < Rr / 4) /\
    (forall z, Cmod z < Rr / 4 -> G z <> C0).
Proof.
  intros F R2 Rr M HR HRR2 HF0 HFptc HFhol HM.
  assert (HR2 : 1 < R2) by lra.
  (* the small disk sits inside both side conditions *)
  assert (Hsmall_peel : forall w : C, Cmod w < Rr / 4 -> Cmod w < (R2 - 1) / 2)
    by (intros w Hw; lra).
  assert (Hshrink : forall G : C -> C, disk_holo G R2 -> disk_holo G (Rr + 1))
    by (intros G HG z Hz; apply HG; lra).
  (* every peel list is short *)
  destruct (peel_length_bound F Rr M HR HF0 HM) as [N HN].
  assert (Hbd : forall n, PeelLen F R2 Rr n -> (n <= N)%nat).
  { intros n [l [G [Hid [Hhol [Hptc [Hsm Hlen]]]]]].
    rewrite <- Hlen.
    apply (HN G l Hid Hptc (Hshrink G Hhol)).
    intros w Hw. left. apply Hsm; exact Hw. }
  (* the empty peel is available *)
  assert (H0 : PeelLen F R2 Rr 0%nat).
  { exists nil, F. split; [ | split; [ | split; [ | split ] ] ].
    - intro z. cbn [prodfac]. ring.
    - exact HFhol.
    - exact HFptc.
    - intros w Hw; destruct Hw.
    - reflexivity. }
  (* so take a maximal one *)
  destruct (bounded_has_max (PeelLen F R2 Rr) N H0 Hbd) as [m [Hm Hmax]].
  destruct Hm as [l [G [Hid [Hhol [Hptc [Hsm Hlen]]]]]].
  exists l, G. split; [ exact Hid | ]. split; [ exact Hhol | ].
  split; [ exact Hptc | ]. split; [ exact Hsm | ].
  (* a remaining zero could be peeled, lengthening the list *)
  intros w Hw HGw.
  destruct (DivBy_cons F G R2 l w HR2 (Hsmall_peel w Hw) Hid Hhol Hptc HGw)
    as [H [Hid' [Hhol' Hptc']]].
  assert (Hlonger : PeelLen F R2 Rr (S m)).
  { exists (w :: l), H. split; [ exact Hid' | ]. split; [ exact Hhol' | ].
    split; [ exact Hptc' | ]. split.
    - intros w' [E | Hin]; [ subst w'; exact Hw | apply Hsm; exact Hin ].
    - cbn [length]. rewrite Hlen. reflexivity. }
  pose proof (Hmax (S m) Hlonger) as Hcontra. lia.
Qed.

Print Assumptions cofactor_zero_free.
