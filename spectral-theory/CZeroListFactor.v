(* ================================================================= *)
(*  CZeroListFactor.v  —  brick 1: iterating the peel over a LIST.      *)
(*                                                                    *)
(*  Turns the one-zero factorisation (CZeroFactorDisk.zero_factor_disk)*)
(*  into the shape jensen_count_D consumes:                            *)
(*                                                                    *)
(*    DivBy F R2 l  :=  exists G,  F = prodfac l . G                   *)
(*                              /\ G holomorphic on Cmod z < R2        *)
(*                              /\ G pointwise-continuous.             *)
(*                                                                    *)
(*    DivBy_nil      : DivBy F R2 nil                                  *)
(*    DivBy_cons     : F = prodfac l . G, G w = C0  ==>  DivBy F R2 (w::l) *)
(*    DivBy_distinct : NoDup l, every w in l a zero of F               *)
(*                       ==>  DivBy F R2 l                             *)
(*                                                                    *)
(*  WHY THE LIST IS AN INPUT, NOT AN OUTPUT.  The tempting statement    *)
(*  is "peel zeros until the cofactor has none left" -- but that is no  *)
(*  structural recursion, and its termination IS the finiteness of the  *)
(*  zero set (the brick after next).  Phrasing the result as            *)
(*  DIVISIBILITY BY A GIVEN LIST makes the induction structural and     *)
(*  discharges no termination obligation; which list to feed it is a    *)
(*  separate question, answered later.                                 *)
(*                                                                    *)
(*  WHERE MULTIPLICITY LIVES.  DivBy_cons asks for  G w = C0  -- the    *)
(*  CURRENT COFACTOR vanishing at w, not F.  That is the whole subtlety:*)
(*   * distinct zeros are free.  If rho <> w and F rho = C0 then from   *)
(*     F rho = (rho - w) . H rho and rho - w <> C0 we get H rho = C0.   *)
(*     That is exactly what DivBy_distinct automates, via               *)
(*     prodfac_ne0_notin.                                              *)
(*   * a REPEATED zero is not.  F = (z - w) . H says nothing about H w. *)
(*     "w has multiplicity >= 2" IS the proposition H w = C0, and a     *)
(*     caller wanting w twice in l must supply it (chain DivBy_cons by  *)
(*     hand).  Proving it is finite-order-of-vanishing, a later brick.  *)
(*                                                                    *)
(*  The radius condition Cmod w < (R2-1)/2 is required of each list      *)
(*  element but never compounds: zero_factor_disk returns a cofactor    *)
(*  holomorphic on the FULL disk Cmod z < R2, so peeling n zeros leaves *)
(*  the domain untouched.  Axiom-clean.                                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CRemovableExtDom
        JensenMultiZero CZeroFactorDisk.
Open Scope R_scope.

(* the two regularity properties the peel preserves *)
Definition disk_holo (G : C -> C) (R2 : R) : Prop :=
  forall z, Cmod z < R2 -> exists d, is_Cderiv G z d.

Definition ptcont (G : C -> C) : Prop :=
  forall z eps, 0 < eps -> exists del, 0 < del /\
    forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (G z') (G z)) < eps.

(* F is divisible by the zero list l, with a cofactor still regular *)
Definition DivBy (F : C -> C) (R2 : R) (l : list C) : Prop :=
  exists G : C -> C,
    (forall z, F z = Cmul (prodfac l z) (G z)) /\ disk_holo G R2 /\ ptcont G.

(* ----------------------------------------------------------------- *)
(*  the product of factors is nonzero off the list                    *)
(*  (JensenCount.prodfac_C0_ne0 is the special case z = C0)           *)
(* ----------------------------------------------------------------- *)
Lemma prodfac_ne0_notin : forall (l : list C) (z : C),
  ~ In z l -> prodfac l z <> C0.
Proof.
  induction l as [| rho l' IH]; intros z Hnin; cbn [prodfac].
  - exact C1_neq_C0.
  - apply Cmul_ne0.
    + apply minus_ne. intro E. apply Hnin. left. symmetry. exact E.
    + apply IH. intro Hin. apply Hnin. right. exact Hin.
Qed.

(* ----------------------------------------------------------------- *)
(*  the empty list: F is its own cofactor                             *)
(* ----------------------------------------------------------------- *)
Lemma DivBy_nil : forall (F : C -> C) (R2 : R),
  disk_holo F R2 -> ptcont F -> DivBy F R2 nil.
Proof.
  intros F R2 Hhol Hptc. exists F. split; [ | split ].
  - intro z. cbn [prodfac]. ring.
  - exact Hhol.
  - exact Hptc.
Qed.

(* ----------------------------------------------------------------- *)
(*  one more peel: the CURRENT COFACTOR must vanish at w              *)
(* ----------------------------------------------------------------- *)
Lemma DivBy_cons : forall (F G : C -> C) (R2 : R) (l : list C) (w : C),
  1 < R2 -> Cmod w < (R2 - 1) / 2 ->
  (forall z, F z = Cmul (prodfac l z) (G z)) ->
  disk_holo G R2 -> ptcont G ->
  G w = C0 ->
  DivBy F R2 (w :: l).
Proof.
  intros F G R2 l w HR2 Hw HFG HGhol HGptc HGw.
  destruct (zero_factor_disk G R2 w HR2 Hw HGptc HGhol HGw)
    as [H [Hid [Hhol Hptc]]].
  exists H. split; [ | split ]; [ | exact Hhol | exact Hptc ].
  intro z. rewrite (HFG z), (Hid z). cbn [prodfac]. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  DISTINCT zeros peel with no extra input: the cofactor's vanishing *)
(*  at the next zero is forced, since the already-peeled product does *)
(*  not vanish there.                                                 *)
(* ----------------------------------------------------------------- *)
Theorem DivBy_distinct : forall (F : C -> C) (R2 : R) (l : list C),
  1 < R2 -> NoDup l ->
  (forall w, In w l -> Cmod w < (R2 - 1) / 2) ->
  (forall w, In w l -> F w = C0) ->
  disk_holo F R2 -> ptcont F ->
  DivBy F R2 l.
Proof.
  intros F R2 l HR2 Hnd Hin Hzero HFhol HFptc.
  revert Hnd Hin Hzero.
  induction l as [| w l' IH]; intros Hnd Hin Hzero.
  - apply DivBy_nil; [ exact HFhol | exact HFptc ].
  - assert (Hnotin : ~ In w l') by (inversion Hnd; assumption).
    assert (Hnd' : NoDup l') by (inversion Hnd; assumption).
    destruct (IH Hnd'
                 (fun r Hr => Hin r (or_intror Hr))
                 (fun r Hr => Hzero r (or_intror Hr)))
      as [G [Hid [Hhol Hptc]]].
    apply (DivBy_cons F G R2 l' w HR2 (Hin w (or_introl eq_refl)) Hid Hhol Hptc).
    (* the forced vanishing: F w = prodfac l' w . G w = C0, first factor <> C0 *)
    assert (HFw : F w = C0) by (apply Hzero; left; reflexivity).
    assert (Hp : prodfac l' w <> C0) by (apply prodfac_ne0_notin; exact Hnotin).
    pose proof (Hid w) as Hidw. rewrite HFw in Hidw.
    assert (Hcancel : Cmul (Cinv (prodfac l' w)) (Cmul (prodfac l' w) (G w)) = G w)
      by (field; exact Hp).
    rewrite <- Hcancel, <- Hidw. ring.
Qed.

Print Assumptions DivBy_distinct.
