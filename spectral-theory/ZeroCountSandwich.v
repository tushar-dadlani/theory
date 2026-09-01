(* ================================================================= *)
(*  ZeroCountSandwich.v  --  how far this development is from RH,     *)
(*  as a theorem rather than as prose.                                *)
(*                                                                    *)
(*  "RH up to height T" is the sandwich N0(T) = N(T): the zeros found  *)
(*  ON the line account for ALL zeros below T.  This file states both  *)
(*  sides of that sandwich at height ~49, with the gap left open:      *)
(*                                                                    *)
(*      9  <=  #zeros in |z| < 50  <=  Bxi 50  ~  731                  *)
(*                                                                    *)
(*  The lower bound is NineZeros.nine_zeros (nine certified sign       *)
(*  changes).  The upper bound is XiZeroDensity.xi_count_below, whose  *)
(*  Jensen majorant is charged for Xi's real-axis growth and so        *)
(*  overshoots the true count (18 in this disk) by a factor of ~40.    *)
(*                                                                    *)
(*  Closing 731 to 9 is exactly what the argument principle would do   *)
(*  and what this repository does not have.  See docs/rh_routes.md.    *)
(*                                                                    *)
(*  NOTE the name collision, deliberate here:                          *)
(*    BerryKeatingDilation.Bxi : R -> C   is  XiC o crit                *)
(*    XiZeroDensity.Bxi        : R -> R   is the counting majorant      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus RiemannXiEntire CoherenceSingularity
        BerryKeatingDilation NineZeros XiZeroDensity.
Import ListNotations.
Open Scope R_scope.

(* spec Bxi t is definitionally XiC (crit t) = C0 *)
Lemma spec_to_zero : forall t,
  spec BerryKeatingDilation.Bxi t -> XiC (crit t) = C0.
Proof. intros t H. exact H. Qed.

Lemma crit_inj : forall a b, crit a = crit b -> a = b.
Proof. intros a b H. exact (f_equal Im H). Qed.

Lemma Re_crit : forall t, Re (crit t) = / 2.
Proof. intro t. reflexivity. Qed.

Lemma Cmod_crit_lt50 : forall t, - 49 < t < 49 -> Cmod (crit t) < 50.
Proof.
  intros t Ht.
  assert (H2500 : sqrt 2500 = 50).
  { replace 2500 with (50 * 50) by ring. apply sqrt_square. lra. }
  unfold Cmod, Cnorm2, crit; cbn [Re Im].
  rewrite <- H2500. apply sqrt_lt_1_alt. split; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The sandwich                                                      *)
(* ----------------------------------------------------------------- *)

Theorem zero_count_sandwich :
  exists l : list C,
    NoDup l
    /\ length l = 9%nat
    /\ (forall rho, In rho l ->
          XiC rho = C0 /\ Re rho = / 2 /\ Cmod rho < 50)
    /\ (forall s : list C, NoDup s ->
          (forall rho, In rho s -> XiC rho = C0) ->
          (forall rho, In rho s -> Cmod rho < 50) ->
          INR (length s) <= XiZeroDensity.Bxi 50).
Proof.
  destruct nine_zeros as [[t0 [Ht0 Hs0]] Hgaps].
  destruct (Hgaps 0%nat ltac:(lia)) as [t1 [Ht1 Hs1]].
  destruct (Hgaps 1%nat ltac:(lia)) as [t2 [Ht2 Hs2]].
  destruct (Hgaps 2%nat ltac:(lia)) as [t3 [Ht3 Hs3]].
  destruct (Hgaps 3%nat ltac:(lia)) as [t4 [Ht4 Hs4]].
  destruct (Hgaps 4%nat ltac:(lia)) as [t5 [Ht5 Hs5]].
  destruct (Hgaps 5%nat ltac:(lia)) as [t6 [Ht6 Hs6]].
  destruct (Hgaps 6%nat ltac:(lia)) as [t7 [Ht7 Hs7]].
  destruct (Hgaps 7%nat ltac:(lia)) as [t8 [Ht8 Hs8]].
  cbn [sq] in Ht1, Ht2, Ht3, Ht4, Ht5, Ht6, Ht7, Ht8.
  exists [crit t0; crit t1; crit t2; crit t3; crit t4;
          crit t5; crit t6; crit t7; crit t8].
  split; [ | split; [ reflexivity | split ] ].
  - (* distinct: the ordinates lie in disjoint gaps *)
    repeat (apply NoDup_cons;
            [ simpl; intro HIn;
              repeat (destruct HIn as [HIn | HIn]);
              solve [ contradiction | apply crit_inj in HIn; lra ]
            | ]).
    apply NoDup_nil.
  - (* each listed point is a zero, on the line, inside the disk *)
    intros rho HIn. simpl in HIn.
    repeat (destruct HIn as [HIn | HIn]); try contradiction; subst rho;
      (split; [ apply spec_to_zero; assumption
              | split; [ apply Re_crit | apply Cmod_crit_lt50; lra ] ]).
  - (* and any set of distinct zeros in the disk is bounded by Bxi 50 *)
    intros s Hnd Hz Hsm.
    apply (xi_count_below 50 s ltac:(lra) Hnd Hz Hsm).
Qed.
