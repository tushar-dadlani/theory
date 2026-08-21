(* ================================================================= *)
(*  CycIndex.v  —  index arithmetic for the cyclic group ring.        *)
(*                                                                    *)
(*    cgp p a z   : congruence mod p, transported into Z              *)
(*    madd, msub  : addition and subtraction of indices mod p         *)
(*    msub_madd, madd_msub_id, msub_invol, msub_per : the four        *)
(*                  identities the ring laws will need                *)
(*    rotation_perm, reflect_perm, mulmod_perm0 : the three           *)
(*                  permutations of seq 0 p                           *)
(*                                                                    *)
(*  THIS FILE EXISTS TO QUARANTINE THE TRUNCATION.  Everything about  *)
(*  a cyclic convolution that can go wrong lives in nat subtraction    *)
(*  under mod, and it goes wrong quietly: a - b is 0 when b > a, so    *)
(*  a false index identity can look plausible and only fail on the     *)
(*  wrap-around cases.  So no fact about msub is proved by reasoning   *)
(*  about mod at all.  Every one goes through a single funnel:         *)
(*                                                                    *)
(*    show both sides are < p, then show they are congruent mod p      *)
(*    as INTEGERS, and conclude by cgp_eq.                             *)
(*                                                                    *)
(*  In Z there is no truncation, so each congruence is a linear        *)
(*  combination of divisibility witnesses that lia checks outright.    *)
(*  That is the same discipline that made cg_psi tractable in          *)
(*  CEisensteinNormJ; here it is adopted from the first line rather    *)
(*  than discovered halfway through.                                   *)
(*                                                                    *)
(*  msub a b IS ONLY MEANINGFUL FOR b <= p, and that hypothesis is     *)
(*  carried explicitly rather than assumed: a + p - b truncates the    *)
(*  moment b exceeds a + p, and b <= p is what rules it out.           *)
(*                                                                    *)
(*  NOTHING HERE MENTIONS Eis, and nothing here needs p prime -- only  *)
(*  mulmod_perm0 does.  Keeping the split sharp means the ring layer   *)
(*  built on top can stay prime-free, which is what lets it be reused  *)
(*  and keeps every downstream signature honest.                       *)
(*                                                                    *)
(*  rotation_perm also exists in DFTConvolution, but that file pulls   *)
(*  in ComplexField and RootsOfUnity -- the classical-Reals half of    *)
(*  the repo.  It is re-proved here in twenty lines so that the        *)
(*  cyclotomic layer's dependency graph stays inside the axiom-free    *)
(*  arithmetic development.                                            *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Require Import ZmodPStar.
Import ListNotations.
Open Scope Z_scope.

Section Index.

Variable p : nat.
Hypothesis Hp1 : (1 <= p)%nat.

Notation P := (Z.of_nat p).

(* ----------------------------------------------------------------- *)
(*  A.  the funnel                                                     *)
(* ----------------------------------------------------------------- *)
Definition cgp (a : nat) (z : Z) : Prop := (P | Z.of_nat a - z).

Lemma cgp_refl : forall a, cgp a (Z.of_nat a).
Proof. intro a. exists 0. ring. Qed.

Lemma cgp_mod : forall a, cgp (a mod p)%nat (Z.of_nat a).
Proof.
  intro a. exists (- Z.of_nat (a / p)%nat).
  assert (E : (a = p * (a / p) + a mod p)%nat) by apply Nat.div_mod_eq. lia.
Qed.

Lemma cgp_step : forall a z z', cgp a z -> (P | z - z') -> cgp a z'.
Proof. intros a z z' [c Hc] [d Hd]. exists (c + d). lia. Qed.

Lemma cgp_eq : forall a b, (a < p)%nat -> (b < p)%nat ->
  (P | Z.of_nat a - Z.of_nat b) -> a = b.
Proof.
  intros a b Ha Hb [c Hc].
  assert (Hrange : - P < Z.of_nat a - Z.of_nat b < P) by lia.
  destruct (Z.lt_trichotomy c 0) as [H | [H | H]].
  - assert (c * P <= (-1) * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - rewrite H in Hc. lia.
  - assert (1 * P <= c * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the two index operations                                       *)
(* ----------------------------------------------------------------- *)
Definition madd (a b : nat) : nat := ((a + b) mod p)%nat.
Definition msub (a b : nat) : nat := ((a + p - b) mod p)%nat.

Lemma madd_lt : forall a b, (madd a b < p)%nat.
Proof. intros a b. unfold madd. apply Nat.mod_upper_bound. lia. Qed.

Lemma msub_lt : forall a b, (msub a b < p)%nat.
Proof. intros a b. unfold msub. apply Nat.mod_upper_bound. lia. Qed.

Lemma madd_cg : forall a b, cgp (madd a b) (Z.of_nat a + Z.of_nat b).
Proof.
  intros a b. unfold madd.
  apply (cgp_step _ (Z.of_nat (a + b)%nat)); [ apply cgp_mod | ].
  exists 0. lia.
Qed.

Lemma msub_cg : forall a b, (b <= p)%nat -> cgp (msub a b) (Z.of_nat a - Z.of_nat b).
Proof.
  intros a b Hb. unfold msub.
  apply (cgp_step _ (Z.of_nat (a + p - b)%nat)); [ apply cgp_mod | ].
  exists 1. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the identities the ring laws need                              *)
(* ----------------------------------------------------------------- *)
Lemma msub_small : forall a, (a < p)%nat -> msub a 0 = a.
Proof.
  intros a Ha. apply cgp_eq; [ apply msub_lt | exact Ha | ].
  destruct (msub_cg a 0 ltac:(lia)) as [c Hc]. exists c. lia.
Qed.

Lemma msub_invol : forall n i, (i < p)%nat -> msub n (msub n i) = i.
Proof.
  intros n i Hi. apply cgp_eq; [ apply msub_lt | exact Hi | ].
  destruct (msub_cg n (msub n i) ltac:(pose proof (msub_lt n i); lia)) as [c Hc].
  destruct (msub_cg n i ltac:(lia)) as [d Hd].
  exists (c - d). lia.
Qed.

Lemma madd_msub_id : forall k i, (k < p)%nat -> (i < p)%nat -> msub (madd k i) i = k.
Proof.
  intros k i Hk Hi. apply cgp_eq; [ apply msub_lt | exact Hk | ].
  destruct (msub_cg (madd k i) i ltac:(lia)) as [c Hc].
  destruct (madd_cg k i) as [d Hd].
  exists (c + d). lia.
Qed.

Lemma msub_madd : forall n k i, (i < p)%nat -> (k < p)%nat ->
  msub n (madd k i) = msub (msub n i) k.
Proof.
  intros n k i Hi Hk. apply cgp_eq; [ apply msub_lt | apply msub_lt | ].
  destruct (msub_cg n (madd k i) ltac:(pose proof (madd_lt k i); lia)) as [c Hc].
  destruct (madd_cg k i) as [d Hd].
  destruct (msub_cg (msub n i) k ltac:(lia)) as [e He].
  destruct (msub_cg n i ltac:(lia)) as [f Hf].
  exists (c - d - e - f). lia.
Qed.

Lemma msub_per : forall n i, (i < p)%nat -> msub n i = msub (n mod p)%nat i.
Proof.
  intros n i Hi. apply cgp_eq; [ apply msub_lt | apply msub_lt | ].
  destruct (msub_cg n i ltac:(lia)) as [c Hc].
  destruct (msub_cg (n mod p)%nat i ltac:(lia)) as [d Hd].
  destruct (cgp_mod n) as [e He].
  exists (c - d - e). lia.
Qed.

Lemma madd_comm : forall a b, madd a b = madd b a.
Proof. intros a b. unfold madd. rewrite Nat.add_comm. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the three permutations of seq 0 p                              *)
(* ----------------------------------------------------------------- *)
Lemma rotation_perm : forall c,
  Permutation (map (fun n => madd n c) (seq 0 p)) (seq 0 p).
Proof.
  intro c. apply NoDup_Permutation_bis.
  - apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros x y Hx Hy Hxy. apply in_seq in Hx. apply in_seq in Hy.
    apply cgp_eq; [ lia | lia | ].
    destruct (madd_cg x c) as [u Hu]. destruct (madd_cg y c) as [v Hv].
    rewrite Hxy in Hu. exists (v - u). lia.
  - rewrite length_map, length_seq. lia.
  - intros z Hz. apply in_map_iff in Hz as [x [Hx _]]. rewrite <- Hx.
    apply in_seq. pose proof (madd_lt x c). lia.
Qed.

Lemma reflect_perm : forall n,
  Permutation (map (msub n) (seq 0 p)) (seq 0 p).
Proof.
  intro n. apply NoDup_Permutation_bis.
  - apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros x y Hx Hy Hxy. apply in_seq in Hx. apply in_seq in Hy.
    apply cgp_eq; [ lia | lia | ].
    destruct (msub_cg n x ltac:(lia)) as [u Hu].
    destruct (msub_cg n y ltac:(lia)) as [v Hv].
    rewrite Hxy in Hu. exists (u - v). lia.
  - rewrite length_map, length_seq. lia.
  - intros z Hz. apply in_map_iff in Hz as [x [Hx _]]. rewrite <- Hx.
    apply in_seq. pose proof (msub_lt n x). lia.
Qed.

Lemma mulmod_perm0 : prime P -> forall m, ~ Nat.divide p m ->
  Permutation (map (fun x => (m * x) mod p)%nat (seq 0 p)) (seq 0 p).
Proof.
  intros Hp m Hm. apply NoDup_Permutation_bis.
  - apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros x y Hx Hy Hxy. apply in_seq in Hx. apply in_seq in Hy.
    pose proof (cancel_mod p m x y Hp Hm Hxy) as He.
    rewrite (Nat.mod_small x p), (Nat.mod_small y p) in He by lia. exact He.
  - rewrite length_map, length_seq. lia.
  - intros z Hz. apply in_map_iff in Hz as [x [Hx _]]. rewrite <- Hx.
    apply in_seq. pose proof (Nat.mod_upper_bound (m * x)%nat p ltac:(lia)). lia.
Qed.

End Index.

Print Assumptions cgp_eq.
Print Assumptions msub_madd.
Print Assumptions madd_msub_id.
Print Assumptions rotation_perm.
Print Assumptions mulmod_perm0.
