(* ================================================================= *)
(*  PsiRIntegrable.v  --  Riemann integrability of the Chebyshev step  *)
(*  function psiR, and of the Newman/Tauberian integrand.              *)
(*                                                                    *)
(*  Prerequisite for the Tauberian squeeze.  Nothing in the repo       *)
(*  integrated psiR, and Stdlib offers integrability only for          *)
(*  CONTINUOUS f (RiemannInt_P6).                                      *)
(*                                                                    *)
(*  The lever: `adapted_couple` constrains a step function only on the *)
(*  OPEN subintervals (constant_D_eq ... (open_interval ...)).  So a   *)
(*  function may be altered at the two endpoints a, b at NO cost --    *)
(*  the same subdivision still works, and RiemannInt_SF is unchanged.  *)
(*  That gives a general transfer lemma:                               *)
(*                                                                    *)
(*      f = g on the OPEN (a,b)  ->  g integrable  ->  f integrable    *)
(*                                                                    *)
(*  psiR is constant on each open cell (N, N+1), and the Tauberian     *)
(*  integrand (psiR t - t)/t^2 agrees there with a CONTINUOUS function,*)
(*  so both follow from RiemannInt_P14 / RiemannInt_P6 plus transfer.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Arith.
Require Import Chebyshev ChebyshevPsiR.
Open Scope R_scope.

Lemma pos_Rl_In : forall (l : list R) (i : nat), (i < length l)%nat ->
  List.In (RList.pos_Rl l i) l.
Proof.
  intros l i Hi.
  apply (proj2 (RList.RList_P3 l (RList.pos_Rl l i))).
  exists i. split; [ reflexivity | exact Hi ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The endpoint spike: same subdivision, same integral.              *)
(* ----------------------------------------------------------------- *)

Definition spikef (a b : R) (ps : StepFun a b) (ma mb : R) (t : R) : R :=
  if Req_dec_T t a then Rmax (ps t) ma
  else if Req_dec_T t b then Rmax (ps t) mb
  else ps t.

Lemma spike_adapt : forall a b (Hab : a <= b) (ps : StepFun a b) (ma mb : R),
  adapted_couple (spikef a b ps ma mb) a b (subdivision ps) (subdivision_val ps).
Proof.
  intros a b Hab ps ma mb.
  pose proof (StepFun_P1 ps) as Hadapt.
  destruct Hadapt as [Ho [H0 [Hn [Hlen Hconst]]]].
  split; [ exact Ho | ]. split; [ exact H0 | ]. split; [ exact Hn | ].
  split; [ exact Hlen | ].
  intros i Hi x Hx.
  assert (Hi2 : (S i < length (subdivision ps))%nat)
    by (rewrite Hlen in Hi |- *; cbn in Hi; lia).
  assert (Ha' : RList.pos_Rl (subdivision ps) 0
                <= RList.pos_Rl (subdivision ps) i).
  { apply RList.RList_P5; [ exact Ho | apply pos_Rl_In; lia ]. }
  assert (Hb' : RList.pos_Rl (subdivision ps) (S i)
                <= RList.pos_Rl (subdivision ps)
                     (pred (length (subdivision ps)))).
  { apply RList.RList_P7; [ exact Ho | apply pos_Rl_In; lia ]. }
  rewrite H0 in Ha'. rewrite Rmin_left in Ha' by exact Hab.
  rewrite Hn in Hb'. rewrite Rmax_right in Hb' by exact Hab.
  destruct Hx as [Hx1 Hx2].
  unfold spikef.
  destruct (Req_dec_T x a) as [He | _]; [ exfalso; lra | ].
  destruct (Req_dec_T x b) as [He | _]; [ exfalso; lra | ].
  exact (Hconst i Hi x (conj Hx1 Hx2)).
Qed.

Definition spike_pre (a b : R) (Hab : a <= b) (ps : StepFun a b) (ma mb : R)
  : IsStepFun (spikef a b ps ma mb) a b :=
  existT _ (subdivision ps)
    (existT _ (subdivision_val ps) (spike_adapt a b Hab ps ma mb)).

Definition spikeSF (a b : R) (Hab : a <= b) (ps : StepFun a b) (ma mb : R)
  : StepFun a b := mkStepFun (spike_pre a b Hab ps ma mb).

Lemma spikeSF_int : forall (a b : R) (Hab : a <= b) (ps : StepFun a b) (ma mb : R),
  RiemannInt_SF (spikeSF a b Hab ps ma mb) = RiemannInt_SF ps.
Proof. intros. unfold RiemannInt_SF. reflexivity. Qed.

Lemma spikeSF_ge : forall (a b : R) (Hab : a <= b) (ps : StepFun a b) (ma mb t : R),
  ps t <= spikeSF a b Hab ps ma mb t.
Proof.
  intros a b Hab ps ma mb t. unfold spikeSF; cbn [fe]; unfold spikef.
  destruct (Req_dec_T t a); [ apply Rmax_l | ].
  destruct (Req_dec_T t b); [ apply Rmax_l | ]. apply Rle_refl.
Qed.

Lemma spikeSF_a : forall (a b : R) (Hab : a <= b) (ps : StepFun a b) (ma mb : R),
  ma <= spikeSF a b Hab ps ma mb a.
Proof.
  intros a b Hab ps ma mb. unfold spikeSF; cbn [fe]; unfold spikef.
  destruct (Req_dec_T a a) as [_ | Hc]; [ apply Rmax_r | exfalso; apply Hc; reflexivity ].
Qed.

Lemma spikeSF_b : forall (a b : R) (Hab : a <= b) (ps : StepFun a b) (ma mb : R), a <> b ->
  mb <= spikeSF a b Hab ps ma mb b.
Proof.
  intros a b Hab ps ma mb Hne. unfold spikeSF; cbn [fe]; unfold spikef.
  destruct (Req_dec_T b a) as [He | _];
    [ exfalso; apply Hne; symmetry; exact He | ].
  destruct (Req_dec_T b b) as [_ | Hc];
    [ apply Rmax_r | exfalso; apply Hc; reflexivity ].
Qed.

(* ----------------------------------------------------------------- *)
(*  THE TRANSFER LEMMA                                                *)
(* ----------------------------------------------------------------- *)

Theorem Riemann_integrable_ext_open : forall (f g : R -> R) (a b : R),
  a <= b ->
  (forall t, a < t < b -> f t = g t) ->
  Riemann_integrable g a b -> Riemann_integrable f a b.
Proof.
  intros f g a b Hab Heq Hg.
  destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heqab];
    [ | subst b; apply RiemannInt_P7 ].
  intro eps.
  destruct (Hg eps) as [phi [ps [Hbound Hint]]].
  exists phi.
  exists (spikeSF a b Hab ps (Rabs (f a - phi a)) (Rabs (f b - phi b))).
  split.
  - intros t Ht.
    rewrite Rmin_left in Ht by lra. rewrite Rmax_right in Ht by lra.
    destruct (Req_dec_T t a) as [He | Hna].
    { subst t. apply spikeSF_a. }
    destruct (Req_dec_T t b) as [He | Hnb].
    { subst t. apply spikeSF_b. lra. }
    assert (Hin : a < t < b) by (destruct Ht; lra).
    rewrite (Heq t Hin).
    eapply Rle_trans; [ | apply spikeSF_ge ].
    apply Hbound. rewrite Rmin_left by lra. rewrite Rmax_right by lra.
    destruct Ht; split; lra.
  - rewrite spikeSF_int. exact Hint.
Qed.

(* ----------------------------------------------------------------- *)
(*  floor of an integer                                               *)
(* ----------------------------------------------------------------- *)

Lemma floorN_INR : forall n : nat, floorN (INR n) = n.
Proof.
  intro n.
  destruct (floorN_spec (INR n) (pos_INR n)) as [H1 H2].
  assert (Hle : (floorN (INR n) <= n)%nat) by (apply INR_le; exact H1).
  assert (Hlt : (n < S (floorN (INR n)))%nat)
    by (apply INR_lt; rewrite S_INR; lra).
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  psiR is integrable: constant on each open cell.                    *)
(* ----------------------------------------------------------------- *)

Lemma psiR_int_cell : forall (N : nat) (a b : R),
  INR N <= a -> a <= b -> b <= INR (S N) -> Riemann_integrable psiR a b.
Proof.
  intros N a b Ha Hab Hb.
  apply (Riemann_integrable_ext_open psiR (fct_cte (psi N)) a b Hab).
  - intros t Ht. unfold fct_cte. apply psiR_step.
    rewrite S_INR in Hb |- *. destruct Ht; split; lra.
  - apply RiemannInt_P14.
Qed.

Lemma psiR_int_k : forall (k : nat) (a b : R), 0 <= a -> a <= b ->
  (floorN b <= floorN a + k)%nat -> Riemann_integrable psiR a b.
Proof.
  induction k as [| k IH]; intros a b Ha Hab Hk.
  - assert (Hb0 : 0 <= b) by lra.
    destruct (floorN_spec a Ha) as [Ha1 Ha2].
    destruct (floorN_spec b Hb0) as [Hb1 Hb2].
    apply (psiR_int_cell (floorN a) a b Ha1 Hab).
    rewrite S_INR.
    assert (INR (floorN b) <= INR (floorN a)) by (apply le_INR; lia).
    lra.
  - destruct (le_gt_dec (floorN b) (floorN a + k)) as [Hle | Hgt].
    + exact (IH a b Ha Hab Hle).
    + assert (Hb0 : 0 <= b) by lra.
      destruct (floorN_spec a Ha) as [Ha1 Ha2].
      destruct (floorN_spec b Hb0) as [Hb1 Hb2].
      assert (Hac : a <= INR (S (floorN a))) by (rewrite S_INR; lra).
      assert (Hcb : INR (S (floorN a)) <= b).
      { apply Rle_trans with (INR (floorN b)); [ apply le_INR; lia | exact Hb1 ]. }
      apply RiemannInt_P24 with (b := INR (S (floorN a))).
      * apply (psiR_int_cell (floorN a) a (INR (S (floorN a))) Ha1 Hac).
        apply Rle_refl.
      * apply (IH (INR (S (floorN a))) b (pos_INR _) Hcb).
        rewrite floorN_INR. lia.
Qed.

Theorem psiR_integrable : forall a b, 0 <= a -> a <= b ->
  Riemann_integrable psiR a b.
Proof.
  intros a b Ha Hab. apply (psiR_int_k (floorN b) a b Ha Hab). lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  The Newman/Tauberian integrand (psiR t - t)/t^2.                   *)
(*  On each open cell it agrees with a CONTINUOUS function, so the     *)
(*  same transfer applies -- no product-of-integrable lemma needed.    *)
(* ----------------------------------------------------------------- *)

Definition tint (t : R) : R := (psiR t - t) / (t * t).

Lemma tint_int_cell : forall (N : nat) (a b : R),
  0 < a -> INR N <= a -> a <= b -> b <= INR (S N) ->
  Riemann_integrable tint a b.
Proof.
  intros N a b Hpos Ha Hab Hb.
  apply (Riemann_integrable_ext_open tint
           (fun t => (psi N - t) / (t * t)) a b Hab).
  - intros t Ht. unfold tint. rewrite (psiR_step N t); [ reflexivity | ].
    rewrite S_INR in Hb |- *. destruct Ht; split; lra.
  - destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | He];
      [ | subst b; apply RiemannInt_P7 ].
    apply RiemannInt_P6; [ exact Hlt | ].
    intros x Hx. assert (Hxx : x * x <> 0) by (destruct Hx; nra).
    reg.
Qed.

Lemma tint_int_k : forall (k : nat) (a b : R), 0 < a -> a <= b ->
  (floorN b <= floorN a + k)%nat -> Riemann_integrable tint a b.
Proof.
  induction k as [| k IH]; intros a b Ha Hab Hk.
  - assert (Ha0 : 0 <= a) by lra. assert (Hb0 : 0 <= b) by lra.
    destruct (floorN_spec a Ha0) as [Ha1 Ha2].
    destruct (floorN_spec b Hb0) as [Hb1 Hb2].
    apply (tint_int_cell (floorN a) a b Ha Ha1 Hab).
    rewrite S_INR.
    assert (INR (floorN b) <= INR (floorN a)) by (apply le_INR; lia).
    lra.
  - destruct (le_gt_dec (floorN b) (floorN a + k)) as [Hle | Hgt].
    + exact (IH a b Ha Hab Hle).
    + assert (Ha0 : 0 <= a) by lra. assert (Hb0 : 0 <= b) by lra.
      destruct (floorN_spec a Ha0) as [Ha1 Ha2].
      destruct (floorN_spec b Hb0) as [Hb1 Hb2].
      assert (Hac : a <= INR (S (floorN a))) by (rewrite S_INR; lra).
      assert (Hcb : INR (S (floorN a)) <= b).
      { apply Rle_trans with (INR (floorN b)); [ apply le_INR; lia | exact Hb1 ]. }
      apply RiemannInt_P24 with (b := INR (S (floorN a))).
      * apply (tint_int_cell (floorN a) a (INR (S (floorN a))) Ha Ha1 Hac).
        apply Rle_refl.
      * apply (IH (INR (S (floorN a))) b ltac:(lra) Hcb).
        rewrite floorN_INR. lia.
Qed.

Theorem tint_integrable : forall a b, 0 < a -> a <= b ->
  Riemann_integrable tint a b.
Proof.
  intros a b Ha Hab. apply (tint_int_k (floorN b) a b Ha Hab). lia.
Qed.

Print Assumptions psiR_integrable.
Print Assumptions tint_integrable.
