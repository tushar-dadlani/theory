(* ================================================================= *)
(*  FirstZeroBridge.v  --  from a computed enclosure to a sign.        *)
(*                                                                    *)
(*  Nothing here runs vm_compute.  It packages the three conversions   *)
(*  a concrete sign proof needs, so that the file which DOES run the   *)
(*  quadrature contains only the computation and the arithmetic:      *)
(*                                                                    *)
(*    msum_encl : Imsum ... = Some (mkI lo hi) -> the real msum lies   *)
(*                between Q2R lo and Q2R hi                            *)
(*    INR_lit   : INR of a nat numeral, through Z (INR is unary, so    *)
(*                INR 8192 must not be reduced by simpl)               *)
(*    Qbound    : Q2R of a computed rational, bounded by a short       *)
(*                decimal, decided by Qle_bool                         *)
(* ================================================================= *)

From Stdlib Require Import QArith Qreals Reals Lra Lia.
Require Import IntervalArith IntervalArithFun IntervalGint
        IntegrandLip CompositeQuad XirSignChange.
Local Open Scope R_scope.

Lemma msum_encl : forall tq hq n lo hi,
  0 <= Q2R hq ->
  Imsum 46 25 32 14 32 12 30 5 4 46 tq hq n = Some (mkI lo hi) ->
  Q2R lo <= msum (gint (Q2R tq)) 0 (Q2R hq) n <= Q2R hi.
Proof.
  intros tq hq n lo hi Hh H.
  pose proof (Imsum_sound 46 25 32 14 32 12 30 5 4 46 tq hq n
                (mkI lo hi) Hh H) as HC.
  unfold Icontains in HC; simpl in HC. exact HC.
Qed.

(* INR is unary: simpl on INR 8192 would build 8192 successors *)
Lemma INR_lit : forall (n : nat) (z : Z), Z.of_nat n = z -> INR n = IZR z.
Proof. intros n z H. rewrite INR_IZR_INZ, H. reflexivity. Qed.

Lemma Qbound_hi : forall (q r : Q), Qle_bool q r = true -> Q2R q <= Q2R r.
Proof. exact Qle_R. Qed.

Lemma Qbound_lo : forall (q r : Q), Qle_bool r q = true -> Q2R r <= Q2R q.
Proof. intros q r H. exact (Qle_R _ _ H). Qed.

(* Extraction WITHOUT destructing the computed term.  o is a bound
   variable here, so `destruct o` is free; the only place the option is
   ever forced is inside the chk lemma's own vm_compute. *)
Lemma extract_ub : forall (o : option Itv) (r : Q) (x : R),
  match o with Some i => Qle_bool (ihi i) r | None => false end = true ->
  (forall i, o = Some i -> Icontains i x) ->
  x <= Q2R r.
Proof.
  intros o r x H Hs. destruct o as [i |]; [ | discriminate ].
  destruct (Hs i eq_refl) as [_ Hh].
  eapply Rle_trans; [ exact Hh | apply Qle_R; exact H ].
Qed.

Lemma extract_lb : forall (o : option Itv) (r : Q) (x : R),
  match o with Some i => Qle_bool r (ilo i) | None => false end = true ->
  (forall i, o = Some i -> Icontains i x) ->
  Q2R r <= x.
Proof.
  intros o r x H Hs. destruct o as [i |]; [ | discriminate ].
  destruct (Hs i eq_refl) as [Hl _].
  eapply Rle_trans; [ apply Qle_R; exact H | exact Hl ].
Qed.

Print Assumptions msum_encl.
Print Assumptions extract_ub.
