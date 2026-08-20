(* ================================================================= *)
(*  XiZeroDensity.v  —  the zero-counting FUNCTION for xi.             *)
(*                                                                    *)
(*    xi_count_below : any NoDup list of zeros of XiC all of modulus   *)
(*      < R has length at most  Bxi R := ln (4 . XiM (8(R+1))) / ln 3. *)
(*                                                                    *)
(*  xi_zero_count produces its list and its Jensen radius              *)
(*  EXISTENTIALLY, which is fine as a statement but useless as an       *)
(*  input: a caller who cares about a particular disk cannot aim it.    *)
(*  This file turns it into a counting function.  Two things make that  *)
(*  work:                                                              *)
(*                                                                    *)
(*   * the LOWER bound Rc/8 <= Rj.  Choosing the circle Rc := 8(R+1)    *)
(*     forces Rj >= R+1 > R, so the disk we care about really is inside *)
(*     the counted one.                                                *)
(*   * COMPLETENESS of the produced list.  Every zero in |z| < Rj is in *)
(*     l, so any NoDup list of such zeros is included in l, and         *)
(*     NoDup_incl_length bounds its length by length l.                *)
(*                                                                    *)
(*  This is the form the Hadamard programme consumes: it is what lets   *)
(*  one count zeros in dyadic annuli and so bound sum 1/|rho|^2.        *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCcontC CPathIntegral
        JensenMultiZero CZeroListFactor CPeelBound
        RiemannXiEntire XiNonzero XiGrowthBound XiZeroCount CDyadicSum.
Open Scope R_scope.

(* the counting majorant *)
Definition Bxi (r : R) : R := ln (4 * XiM (8 * (r + 1))) / ln 3.

Theorem xi_count_below : forall (r : R) (s : list C),
  0 < r -> NoDup s ->
  (forall rho, In rho s -> XiC rho = C0) ->
  (forall rho, In rho s -> Cmod rho < r) ->
  INR (length s) <= Bxi r.
Proof.
  intros r s HR Hnd Hzero Hsmall.
  destruct (xi_zero_count (8 * (r + 1)) ltac:(lra))
    as [l [Rj [HRj0 [HRjb [HRjlo [Hin [Hzl [Hcomp [Hcount _]]]]]]]]].
  (* the lower bound on Rj puts our disk strictly inside the counted one *)
  assert (HRRj : r < Rj) by lra.
  (* completeness: s is included in l *)
  assert (Hincl : incl s l).
  { intros rho Hrho. apply Hcomp.
    - apply Rlt_trans with r; [ apply Hsmall; exact Hrho | exact HRRj ].
    - apply Hzero; exact Hrho. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  unfold Bxi.
  apply Rle_trans with (INR (length l)); [ apply le_INR; exact Hlen | exact Hcount ].
Qed.

Print Assumptions xi_count_below.

(* ================================================================= *)
(*  THE GENUS-1 CONVERGENCE INPUT for the Hadamard product.            *)
(*                                                                    *)
(*  Feeding xi_count_below to CDyadicSum.dyadic_sum_bound turns the    *)
(*  counting bound into a SUMMABILITY bound:  sum 1/|rho|^2 over any    *)
(*  finite set of zeros of xi of modulus >= 1 is at most 4a.           *)
(*                                                                    *)
(*  HONEST STATUS.  This is a REDUCTION, not yet an unconditional       *)
(*  theorem: the growth hypothesis Hgrow -- that Bxi (2^{k+1}) is       *)
(*  O((k+1) 2^k) -- is left as a hypothesis.  It is TRUE, and true      *)
(*  with a modest explicit constant (a = 12 comfortably suffices,       *)
(*  since Bxi(2^{k+1}) ~ 2^k (11.8 + 5.05 k) by the leading             *)
(*  (t/2) ln (t/pi) term of ln Tgb with t = 16.2^k + 9).  Discharging   *)
(*  it needs numeric control of Rpower, exp, ln and pi that this        *)
(*  development does not yet have -- see the note in the file header    *)
(*  of CDyadicSum.  Everything ELSE in the chain is unconditional.      *)
(* ================================================================= *)
Theorem xi_sum_inv_sq : forall a : R,
  0 <= a ->
  (forall k : nat, Bxi (2 ^ (S k)) <= a * INR (S k) * 2 ^ k) ->
  forall s : list C,
    NoDup s ->
    (forall x, In x s -> XiC x = C0) ->
    (forall x, In x s -> 1 <= Cmod x) ->
    sumlist invsq s <= 4 * a.
Proof.
  intros a Ha Hgrow s Hnd HP Hlow.
  exact (dyadic_sum_bound (fun z => XiC z = C0) Bxi (fun l => NoDup l)
           (fun p l Hl => NoDup_filter p Hl) xi_count_below
           a Ha Hgrow s Hnd HP Hlow).
Qed.

Print Assumptions xi_sum_inv_sq.

(* ================================================================= *)
(*  THE MULTIPLICITY VERSION.                                          *)
(*                                                                    *)
(*  xi_sum_inv_sq above counts each zero ONCE (NoDup).  The Hadamard   *)
(*  product repeats a zero according to its multiplicity, so it needs  *)
(*  the sum over a list that may repeat.  The admissible lists are the *)
(*  PEEL LISTS: those l for which xi = prodfac l . G with G still       *)
(*  regular.  Repeats are exactly what a peel list records.           *)
(*                                                                    *)
(*  Two facts make this work with no new analysis:                     *)
(*   * peel lists are closed under filter (a sublist of a peel list is *)
(*     one -- push the discarded factors into the cofactor), which is   *)
(*     all the dyadic argument asked NoDup for;                        *)
(*   * CPeelBound.peel_count_explicit already counts WITH multiplicity, *)
(*     and taking the circle radius Rc := 8(r+1) makes its bound come   *)
(*     out as exactly Bxi r -- so the SAME majorant, and hence the same *)
(*     xi_Hgrow, is reused unchanged.                                  *)
(* ================================================================= *)
Definition XiPeel (s : list C) : Prop :=
  exists G : C -> C,
    (forall z, XiC z = Cmul (prodfac s z) (G z)) /\
    ptcont G /\ (forall R2, disk_holo G R2).

Lemma prodfac_holo : forall (l : list C) (z : C),
  exists d, is_Cderiv (prodfac l) z d.
Proof.
  induction l as [| w l' IH]; intro z.
  - exists C0. exact (Cderiv_const C1 z).
  - destruct (IH z) as [d Hd]. eexists.
    change (prodfac (w :: l')) with (fun u => Cmul (Cminus u w) (prodfac l' u)).
    apply (Cderiv_mul (fun u => Cminus u w) (prodfac l') z (Cminus C1 C0) d).
    + apply (Cderiv_minus (fun u => u) (fun _ => w) z C1 C0);
        [ apply Cderiv_id | apply Cderiv_const ].
    + exact Hd.
Qed.

Lemma prodfac_filter_split : forall (p : C -> bool) (l : list C) (z : C),
  prodfac l z
  = Cmul (prodfac (filter p l) z) (prodfac (filter (fun x => negb (p x)) l) z).
Proof.
  intros p l z. induction l as [| w l' IH]; cbn [filter].
  - cbn [prodfac]. ring.
  - destruct (p w); cbn [prodfac negb]; rewrite IH; ring.
Qed.

Lemma XiPeel_filter : forall (p : C -> bool) (s : list C),
  XiPeel s -> XiPeel (filter p s).
Proof.
  intros p s [G [Hid [Hptc Hhol]]].
  set (G' := fun z => Cmul (prodfac (filter (fun x => negb (p x)) s) z) (G z)).
  assert (Hhol' : forall z, exists d, is_Cderiv G' z d).
  { intro z.
    destruct (prodfac_holo (filter (fun x => negb (p x)) s) z) as [d1 Hd1].
    destruct (Hhol (Cmod z + 1) z ltac:(lra)) as [d2 Hd2].
    unfold G'. eexists. apply Cderiv_mul; [ exact Hd1 | exact Hd2 ]. }
  exists G'. split; [ | split ].
  - intro z. unfold G'. rewrite (Hid z), (prodfac_filter_split p s z). ring.
  - exact (holo_ptcont G' Hhol').
  - intros R2 z _. apply Hhol'.
Qed.

Theorem xi_count_peel : forall (r : R) (s : list C),
  0 < r -> XiPeel s ->
  (forall x, In x s -> Cmod x < r) ->
  INR (length s) <= Bxi r.
Proof.
  intros r s HR [G [Hid [Hptc Hhol]]] Hsmall.
  set (Rc := 8 * (r + 1)).
  assert (HRc : 0 < Rc) by (unfold Rc; lra).
  assert (Hsm4 : forall w, In w s -> Cmod w <= Rc / 4).
  { intros w Hw. pose proof (Hsmall w Hw) as Hw'. unfold Rc. lra. }
  pose proof (peel_count_explicit XiC G Rc (XiM Rc) s HRc XiC_ne0_at0 Hid Hptc
                (Hhol (Rc + 1)) (XiC_circle_bound Rc HRc) Hsm4) as Hpc.
  rewrite Cmod_XiC_C0 in Hpc.
  replace (2 * XiM Rc / / 2) with (4 * XiM Rc) in Hpc by field.
  unfold Bxi. fold Rc. exact Hpc.
Qed.

Theorem xi_sum_inv_sq_mult : forall a : R,
  0 <= a ->
  (forall k : nat, Bxi (2 ^ (S k)) <= a * INR (S k) * 2 ^ k) ->
  forall s : list C,
    XiPeel s ->
    (forall x, In x s -> XiC x = C0) ->
    (forall x, In x s -> 1 <= Cmod x) ->
    sumlist invsq s <= 4 * a.
Proof.
  intros a Ha Hgrow s Hpeel HP Hlow.
  exact (dyadic_sum_bound (fun z => XiC z = C0) Bxi XiPeel XiPeel_filter
           (fun r s' Hr Hq _ Hsm => xi_count_peel r s' Hr Hq Hsm)
           a Ha Hgrow s Hpeel HP Hlow).
Qed.

Print Assumptions xi_sum_inv_sq_mult.
