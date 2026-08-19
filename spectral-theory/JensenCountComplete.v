(* ================================================================= *)
(*  JensenCountComplete.v  —  the Jensen count with NO cofactor         *)
(*  hypothesis left: everything is discharged from F alone.             *)
(*                                                                    *)
(*    jensen_count_complete : F pointwise-continuous and holomorphic    *)
(*      on Cmod z < RB, with 0 < Rc, Rc + 1 < RB, F C0 <> C0, and       *)
(*      |F| <= M on the circle |z| = Rc, produces a zero list l and a   *)
(*      Jensen radius Rj with                                          *)
(*                                                                    *)
(*        every rho in l a genuine zero, 0 < |rho| < Rj                *)
(*        l COMPLETE: every zero of F in |z| < Rj is in l              *)
(*        INR (length l) <= ln (2 M / |F(0)|) / ln 3   -- the COUNT     *)
(*        (#{rho in l : |rho| <= Rj/2}) . ln 2                          *)
(*            <= (1/2PI) INT ln|F(Rj e^{it})| dt - ln|F(0)|.           *)
(*                                                                    *)
(*  This closes the chain that began with the disk-Jensen re-plumb.     *)
(*  Nothing is left as a hypothesis about a cofactor: HGne0 comes from  *)
(*  CZeroFree.cofactor_zero_free (a maximal peel list), the named       *)
(*  derivative pair from CDerivHoloDisk.holo_deriv_fun_radius, and the  *)
(*  factorisation from CZeroListFactor.                                *)
(*                                                                    *)
(*  RADIUS BOOKKEEPING.  jensen_multi_zero_D wants the cofactor         *)
(*  zero-free on a disk STRICTLY LARGER than the Jensen circle, and     *)
(*  every listed zero STRICTLY INSIDE that circle -- i.e. no zero in    *)
(*  the annulus.  That is satisfiable precisely because the list is     *)
(*  finite: take rho_max, the largest modulus in l (list_max_mod), and  *)
(*  slot the Jensen radius Rj into the gap (rho_max, Rc/4), with the    *)
(*  zero-free radius pinned at Rc/4.  Axiom-clean.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Classical.
Require Import ComplexField Cmodulus Holomorphic CDeriv CPathIntegral CSegInt
        JensenMultiZero JensenCount JensenCountZeros
        CZeroListFactor CPeelBound CZeroFree.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  small list facts about prodfac and the largest modulus            *)
(* ----------------------------------------------------------------- *)
Lemma prodfac_zero_in : forall (l : list C) (w : C), In w l -> prodfac l w = C0.
Proof.
  induction l as [| rho l' IH]; intros w Hin; [ destruct Hin | ].
  cbn [prodfac]. destruct Hin as [E | Hin'].
  - subst rho. replace (Cminus w w) with C0 by ring. ring.
  - rewrite (IH w Hin'). ring.
Qed.

Lemma prodfac_zero_inv : forall (l : list C) (z : C), prodfac l z = C0 -> In z l.
Proof.
  intros l z Hz. destruct (classic (In z l)) as [Hin | Hnin]; [ exact Hin | ].
  exfalso. exact (prodfac_ne0_notin l z Hnin Hz).
Qed.

Lemma list_max_mod : forall (l : list C) (b : R), 0 < b ->
  (forall w, In w l -> Cmod w < b) ->
  exists r, 0 <= r < b /\ forall w, In w l -> Cmod w <= r.
Proof.
  induction l as [| w l' IH]; intros b Hb Hsm.
  - exists 0. split; [ lra | intros x Hx; destruct Hx ].
  - destruct (IH b Hb (fun x Hx => Hsm x (or_intror Hx))) as [r [[Hr0 Hrb] Hr]].
    exists (Rmax (Cmod w) r). split.
    + split.
      * apply Rle_trans with r; [ exact Hr0 | apply Rmax_r ].
      * apply Rmax_lub_lt; [ apply Hsm; left; reflexivity | exact Hrb ].
    + intros x [E | Hx].
      * subst x. apply Rmax_l.
      * apply Rle_trans with r; [ apply Hr; exact Hx | apply Rmax_r ].
Qed.

(* ----------------------------------------------------------------- *)
(*  THE CAPSTONE                                                       *)
(* ----------------------------------------------------------------- *)
Theorem jensen_count_complete : forall (F : C -> C) (RB Rc M : R),
  0 < Rc -> Rc + 1 < RB ->
  F C0 <> C0 ->
  ptcont F ->
  disk_holo F RB ->
  (forall u, Cmod (F (arc Rc u)) <= M) ->
  exists (l : list C) (Rj : R),
    0 < Rj /\ Rj < Rc / 4 /\
    (forall rho, In rho l -> 0 < Cmod rho < Rj) /\
    (forall rho, In rho l -> F rho = C0) /\
    (forall z, Cmod z < Rj -> F z = C0 -> In z l) /\
    INR (length l) <= ln (2 * M / Cmod (F C0)) / ln 3 /\
    forall pr : Riemann_integrable (fun t => ln (Cmod (F (arc Rj t)))) 0 (2 * PI),
      INR (count_le (Rj / 2) l) * ln 2
      <= RiemannInt pr / (2 * PI) - ln (Cmod (F C0)).
Proof.
  intros F RB Rc M HRc HRcB HF0 HFptc HFhol HM.
  destruct (cofactor_zero_free F RB Rc M HRc HRcB HF0 HFptc HFhol HM)
    as [l [G [Hid [Hhol [Hptc [Hsm Hne0]]]]]].
  (* slot the Jensen radius into the gap above the largest zero *)
  destruct (list_max_mod l (Rc / 4) ltac:(lra) Hsm) as [rmax [[Hr0 Hrb] Hr]].
  set (Rj := (rmax + Rc / 4) / 2).
  assert (HRj0 : 0 < Rj) by (unfold Rj; lra).
  assert (HRjb : Rj < Rc / 4) by (unfold Rj; lra).
  assert (HrRj : rmax < Rj) by (unfold Rj; lra).
  exists l, Rj. split; [ exact HRj0 | ]. split; [ exact HRjb | ].
  (* every listed point is a genuine nonzero zero of F *)
  assert (Hzero : forall rho, In rho l -> F rho = C0).
  { intros rho Hin. rewrite (Hid rho), (prodfac_zero_in l rho Hin). ring. }
  assert (Hin_pos : forall rho, In rho l -> 0 < Cmod rho < Rj).
  { intros rho Hin. split.
    - destruct (Cmod_nonneg rho) as [Hlt | Heq]; [ exact Hlt | exfalso ].
      assert (Hrho0 : rho = C0) by (apply (proj1 (Cmod0 rho)); symmetry; exact Heq).
      subst rho. exact (HF0 (Hzero C0 Hin)).
    - apply Rle_lt_trans with rmax; [ apply Hr; exact Hin | exact HrRj ]. }
  split; [ exact Hin_pos | ]. split; [ exact Hzero | ].
  (* completeness: G has no zeros in the disk, so every zero of F is listed *)
  assert (Hcomplete : forall z, Cmod z < Rj -> F z = C0 -> In z l).
  { intros z Hz HFz. apply prodfac_zero_inv.
    assert (HGz : G z <> C0) by (apply Hne0; lra).
    pose proof (Hid z) as Hidz. rewrite HFz in Hidz.
    destruct (classic (prodfac l z = C0)) as [Hp | Hp]; [ exact Hp | exfalso ].
    exact (Cmul_ne0 (prodfac l z) (G z) Hp HGz (eq_sym Hidz)). }
  split; [ exact Hcomplete | ].
  (* the explicit count bound, straight from the decay estimate *)
  split.
  { apply (peel_count_explicit F G Rc M l HRc HF0 Hid Hptc);
      [ intros z Hz; apply Hhol; lra | exact HM | ].
    intros w Hw. left. apply Hsm; exact Hw. }
  (* and now the Jensen count, with the cofactor zero-free on Cmod z < Rc/4 *)
  apply (jensen_count_zeros F G (Rc / 4) Rj l HRj0 HRjb Hid Hptc).
  - intros z Hz. apply Hhol. lra.
  - intros z Hz. apply Hne0. exact Hz.
  - exact Hin_pos.
Qed.

Print Assumptions jensen_count_complete.
