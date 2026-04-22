(** Zone.v — Zone partition with axioms as propositions.

    A ZonePartition decomposes a grid into four masks:
      Cause (C), Observer (O), Effect (E), Kernel (K)
    subject to axioms that enforce the (C,O,E,lift) triple structure.
*)

From ARC Require Import Grid.

(** Mask over a grid: a boolean predicate on positions *)
Definition Mask (r c : nat) : Type := Fin r -> Fin c -> bool.

(** Empty mask: all false *)
Definition empty_mask {r c} : Mask r c := fun _ _ => false.

(** Full mask: all true *)
Definition full_mask {r c} : Mask r c := fun _ _ => true.

(** Mask intersection *)
Definition mask_and {r c} (m1 m2 : Mask r c) : Mask r c :=
  fun i j => andb (m1 i j) (m2 i j).

(** Mask union *)
Definition mask_or {r c} (m1 m2 : Mask r c) : Mask r c :=
  fun i j => orb (m1 i j) (m2 i j).

(** Mask complement *)
Definition mask_not {r c} (m : Mask r c) : Mask r c :=
  fun i j => negb (m i j).

(** Mask subset *)
Definition mask_subset {r c} (m1 m2 : Mask r c) : Prop :=
  forall i j, m1 i j = true -> m2 i j = true.

(** Mask disjointness *)
Definition mask_disjoint {r c} (m1 m2 : Mask r c) : Prop :=
  forall i j, m1 i j = true -> m2 i j = false.

(** ZonePartition: (C, O, E, K) with axioms *)
Record ZonePartition (r c : nat) : Type := mkZonePartition {
  cause    : Mask r c;
  observer : Mask r c;
  effect   : Mask r c;
  kernel   : Mask r c;

  (** Axiom 1: C ∩ E = ∅ — cause and effect zones are disjoint *)
  ax1_disjoint : forall i j,
    cause i j = true -> effect i j = false;

  (** Axiom 2: O ∉ C ∪ E — observer is pure boundary *)
  ax2_boundary : forall i j,
    observer i j = true ->
    cause i j = false /\ effect i j = false;

  (** Axiom 3: C ∪ O ∪ E = S — zones cover the substrate *)
  ax3_covers : forall i j,
    cause i j = true \/ observer i j = true \/ effect i j = true;

  (** Axiom 6: kernel(lift) ⊆ C — what cannot cross stays in cause *)
  ax6_kernel : forall i j,
    kernel i j = true -> cause i j = true;
}.

Arguments mkZonePartition {r c}.
Arguments cause {r c}.
Arguments observer {r c}.
Arguments effect {r c}.
Arguments kernel {r c}.

(** Derived properties *)

(** O is disjoint from C *)
Lemma observer_disjoint_cause : forall r c (zp : ZonePartition r c) i j,
  observer zp i j = true -> cause zp i j = false.
Proof.
  intros. destruct (ax2_boundary _ _ zp i j H). auto.
Qed.

(** O is disjoint from E *)
Lemma observer_disjoint_effect : forall r c (zp : ZonePartition r c) i j,
  observer zp i j = true -> effect zp i j = false.
Proof.
  intros. destruct (ax2_boundary _ _ zp i j H). auto.
Qed.

(** Each cell belongs to exactly one zone *)
Lemma zone_exclusive : forall r c (zp : ZonePartition r c) i j,
  (cause zp i j = true /\ observer zp i j = false /\ effect zp i j = false) \/
  (cause zp i j = false /\ observer zp i j = true /\ effect zp i j = false) \/
  (cause zp i j = false /\ observer zp i j = false /\ effect zp i j = true).
Proof.
  intros.
  destruct (ax3_covers _ _ zp i j) as [Hc | [Ho | He]].
  - left. split; auto.
    split.
    + destruct (observer zp i j) eqn:E; auto.
      exfalso. destruct (ax2_boundary _ _ zp i j E). rewrite H in Hc. discriminate.
    + apply (ax1_disjoint _ _ zp i j Hc).
  - right. left. split.
    + apply (observer_disjoint_cause _ _ zp i j Ho).
    + split; auto.
      apply (observer_disjoint_effect _ _ zp i j Ho).
  - right. right. split.
    + destruct (cause zp i j) eqn:Ec; auto.
      exfalso. pose proof (ax1_disjoint _ _ zp i j Ec). rewrite H in He. discriminate.
    + split.
      * destruct (observer zp i j) eqn:Eo; auto.
        exfalso. destruct (ax2_boundary _ _ zp i j Eo).
        rewrite H0 in He. discriminate.
      * auto.
Qed.
