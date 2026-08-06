(* ================================================================= *)
(*  LiouvilleSign.v  —  the sign monoid IS the Liouville/PNT sign.     *)
(*                                                                    *)
(*  Unifies the {I,N,F} thread with PNT: the Z/2 = {I,N} unit group    *)
(*  (INFMonoid) is the value group of the completely-multiplicative    *)
(*  sign; a sign character g factors as  g = val o tosym  through it    *)
(*  (tosym_hom, val_tosym).  The prime-2 filter gives the dyadic self-  *)
(*  reference  L(x) = L_odd(x) - L(x/2)  (L_split), since g(2m) = -g(m).*)
(*  PNT is exactly the mean of this sign going to 0 (liouville_pnt) --  *)
(*  the parity boundary: the sign STRUCTURE is here, the CANCELLATION   *)
(*  (PNT) is not.  Concrete Omega-Liouville + the equivalence deferred. *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List ZArith.
Require Import INFMonoid RealMobius MobiusOverD.
Import ListNotations.
Open Scope R_scope.

(* ---- generic Rls helpers ---- *)
Lemma Rls_add : forall (l : list nat) (f h : nat -> R),
  Rls l (fun n => f n + h n) = Rls l f + Rls l h.
Proof.
  induction l as [|a l IH]; intros f h;
    [ rewrite !Rls_nil2; ring | rewrite !Rls_cons, IH; ring ].
Qed.

Lemma Rls_opp : forall (l : list nat) (f : nat -> R),
  Rls l (fun n => - f n) = - Rls l f.
Proof.
  induction l as [|a l IH]; intros f;
    [ rewrite !Rls_nil2; ring | rewrite !Rls_cons, IH; ring ].
Qed.

Lemma Rls_filter_ind : forall (p : nat -> bool) (h : nat -> R) (l : list nat),
  Rls l (fun n => if p n then h n else 0) = Rls (filter p l) h.
Proof.
  intros p h l; induction l as [|a l IH];
    [ cbn [filter]; rewrite !Rls_nil2; reflexivity | ].
  cbn [filter]; rewrite Rls_cons; destruct (p a) eqn:Ha.
  - rewrite Rls_cons, IH; reflexivity.
  - rewrite IH; lra.
Qed.

Lemma Rls_map : forall (f : nat -> nat) (h : nat -> R) (l : list nat),
  Rls (map f l) h = Rls l (fun n => h (f n)).
Proof.
  intros f h l; induction l as [|a l IH];
    [ cbn [map]; rewrite !Rls_nil2; reflexivity | ].
  cbn [map]; rewrite !Rls_cons, IH; reflexivity.
Qed.

(* ---- parity of 2k, 2k+1, 2k+2 ---- *)
Lemma even_2k : forall k, Nat.even (2 * k) = true.
Proof.
  induction k as [|k IH]; [ reflexivity | ].
  replace (2 * S k)%nat with (S (S (2 * k)))%nat by lia; exact IH.
Qed.

Lemma odd_2k1 : forall k, Nat.even (S (2 * k)) = false.
Proof.
  intros k; rewrite Nat.even_succ, <- Nat.negb_even, even_2k; reflexivity.
Qed.

(* ---- the prime-2 reindex: even numbers in [1,x] = {2,4,...,2*(x/2)} ---- *)
Lemma even_filter_double : forall k,
  filter Nat.even (seq 1 (2 * k)) = map (fun m => 2 * m)%nat (seq 1 k).
Proof.
  induction k as [|k IH]; [ reflexivity | ].
  replace (2 * S k)%nat with (2 * k + 2)%nat by lia.
  rewrite List.seq_app, filter_app, IH.
  assert (He1 : Nat.even (1 + 2 * k) = false)
    by (replace (1 + 2 * k)%nat with (S (2 * k)) by lia; apply odd_2k1).
  assert (He2 : Nat.even (S (1 + 2 * k)) = true)
    by (replace (S (1 + 2 * k))%nat with (2 * S k)%nat by lia; apply even_2k).
  assert (Hf : filter Nat.even (seq (1 + 2 * k) 2) = [2 * S k]%nat).
  { cbn [seq]; cbn [filter]; rewrite He1; cbn [filter]; rewrite He2; cbn [filter];
      f_equal; lia. }
  rewrite Hf, List.seq_S, map_app; cbn [map]; f_equal; f_equal; lia.
Qed.

Lemma even_filter : forall x,
  filter Nat.even (seq 1 x) = map (fun m => 2 * m)%nat (seq 1 (x / 2)).
Proof.
  intros x; destruct (Nat.Even_or_Odd x) as [[k Hk] | [k Hk]]; subst x.
  - rewrite even_filter_double; do 2 f_equal;
      rewrite Nat.mul_comm, (Nat.div_mul k 2 ltac:(lia)); reflexivity.
  - replace (2 * k + 1)%nat with (S (2 * k)) by lia.
    rewrite List.seq_S, filter_app, even_filter_double.
    assert (He : Nat.even (1 + 2 * k) = false)
      by (replace (1 + 2 * k)%nat with (S (2 * k)) by lia; apply odd_2k1).
    cbn [filter]; rewrite He; cbn [filter]; rewrite app_nil_r.
    do 2 f_equal.
    replace (S (2 * k))%nat with (k * 2 + 1)%nat by lia.
    rewrite (Nat.div_add_l k 2 1 ltac:(lia)), (Nat.div_small 1 2 ltac:(lia)); lia.
Qed.

(* ================================================================= *)
(*  THE SIGN GROUP  Z/2 = {I,N}  (reuse INFMonoid)                     *)
(* ================================================================= *)
Lemma sign_units : forall a : Sym, is_unit a <-> (a = I \/ a = N).
Proof.
  intros [| |]; split; intro H;
    [ left; reflexivity | apply I_unit
    | right; reflexivity | apply N_unit
    | exfalso; exact (F_not_unit H) | destruct H; discriminate ].
Qed.

(* ================================================================= *)
(*  A SIGN CHARACTER g FACTORS THROUGH THE SIGN GROUP:  g = val o tosym *)
(* ================================================================= *)
Section Sign.

Variable g : nat -> Z.
Hypothesis g1 : g 1%nat = 1%Z.
Hypothesis gmult : forall m n, (1 <= m)%nat -> (1 <= n)%nat -> g (m * n)%nat = (g m * g n)%Z.
Hypothesis gsign : forall n, (1 <= n)%nat -> g n = 1%Z \/ g n = (-1)%Z.
Hypothesis g2 : g 2%nat = (-1)%Z.

Definition tosym (n : nat) : Sym := if Z.eqb (g n) 1 then I else N.

Theorem tosym_hom : forall m n, (1 <= m)%nat -> (1 <= n)%nat ->
  tosym (m * n)%nat = op (tosym m) (tosym n).
Proof.
  intros m n Hm Hn; unfold tosym; rewrite (gmult m n Hm Hn).
  destruct (gsign m Hm) as [Hgm | Hgm]; destruct (gsign n Hn) as [Hgn | Hgn];
    rewrite Hgm, Hgn; reflexivity.
Qed.

Theorem val_tosym : forall n, (1 <= n)%nat -> val (tosym n) = g n.
Proof.
  intros n Hn; unfold tosym; destruct (gsign n Hn) as [H | H]; rewrite H; reflexivity.
Qed.

(* ================================================================= *)
(*  THE PRIME-2 DYADIC FILTER:  L(x) = L_odd(x) - L(x/2)               *)
(* ================================================================= *)
Definition L (x : nat) : R := Rls (seq 1 x) (fun n => IZR (g n)).
Definition Lodd (x : nat) : R :=
  Rls (seq 1 x) (fun n => if negb (Nat.even n) then IZR (g n) else 0).

(* the even part of L over [1,x] is  -L(x/2)  (via g(2m) = -g(m)) *)
Theorem L_even : forall x,
  Rls (seq 1 x) (fun n => if Nat.even n then IZR (g n) else 0) = - L (x / 2).
Proof.
  intros x. rewrite Rls_filter_ind, even_filter, Rls_map.
  unfold L. rewrite <- Rls_opp. apply Rls_ext; intros m Hm; apply in_seq in Hm.
  rewrite (gmult 2 m ltac:(lia) ltac:(lia)), g2.
  rewrite <- opp_IZR; f_equal; ring.
Qed.

(* the dyadic self-reference the whole discussion turned on *)
Theorem L_split : forall x, L x = Lodd x - L (x / 2).
Proof.
  intros x. unfold L, Lodd.
  rewrite (Rls_ext _ (fun n => IZR (g n))
             (fun n => (if negb (Nat.even n) then IZR (g n) else 0)
                       + (if Nat.even n then IZR (g n) else 0))).
  - rewrite Rls_add. fold (Lodd x).
    pose proof (L_even x) as He. unfold L in He.
    change (Rls (seq 1 x) (fun n => if Nat.even n then IZR (g n) else 0))
      with (Rls (seq 1 x) (fun n => if Nat.even n then IZR (g n) else 0)) in *.
    rewrite He; unfold Lodd; ring.
  - intros n _; destruct (Nat.even n); simpl; ring.
Qed.

(* ---- the target, STATED (not proved): PNT <-> mean of the sign -> 0 ----
   the parity boundary -- structure (tosym/val_tosym) is here, the
   cancellation (liouville_pnt) is exactly what PNT provides and no
   sign-group structure yields. *)
Definition liouville_pnt : Prop := Un_cv (fun x => L x / INR x) 0.

End Sign.

Print Assumptions tosym_hom.
Print Assumptions L_split.

(* ================================================================= *)
(*  END LiouvilleSign.v  —  the {I,N,F} sign monoid = the Liouville     *)
(*  sign; g = val o tosym; L(x) = L_odd(x) - L(x/2); PNT = mean -> 0.   *)
(* ================================================================= *)
