(* ================================================================= *)
(*  R2Count.v                                                        *)
(*                                                                    *)
(*  THE SUM-OF-TWO-SQUARES COUNTING FUNCTION  r2(n)  and two of its   *)
(*  structural facts (Jacobi's-formula territory), AXIOM-FREE.        *)
(*                                                                    *)
(*  r2(n) counts the integer pairs (a,b) with a^2 + b^2 = n.  We      *)
(*  realise it as the length of a decidable bounded search over the    *)
(*  box [-floor(sqrt n), floor(sqrt n)]^2 (SumTwoSquares forces        *)
(*  |a|,|b| <= sqrt n).  Two theorems:                                *)
(*                                                                    *)
(*    (1)  r2(n) > 0  <->  n is a sum of two squares (sum2 n),         *)
(*         and hence, by TwoSquaresFull, for n > 0                     *)
(*             r2(n) > 0  <->  every prime q = 3 (mod 4) divides n     *)
(*                            to an even power  (q3even n).            *)
(*         -- the FULL arithmetic characterisation of when the count   *)
(*         is nonzero.                                                *)
(*                                                                    *)
(*    (2)  4 | r2(n)  for every n > 0.                                 *)
(*         This is the factor of 4 in Jacobi's formula                 *)
(*             r2(n) = 4 * (d_1(n) - d_3(n)),                          *)
(*         proved here directly: the rotation (a,b) |-> (-b,a) (mult   *)
(*         by the Gaussian unit i) is a FIXED-POINT-FREE order-4        *)
(*         action on the solution set, so solutions come in orbits of   *)
(*         size exactly 4.  (The full Jacobi count d_1 - d_3 is a       *)
(*         deeper theta/Gaussian-integer result, not attempted here.)  *)
(*                                                                    *)
(*  Everything is over Z / nat / lists -- no Reals -- so this file is   *)
(*  AXIOM-FREE ("Closed under the global context").                   *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Wf_nat.
Require Import SumTwoSquares TwoSquaresFull.
Import ListNotations.

(* ================================================================= *)
(*  §0  two generic NoDup helpers (Stdlib lacks the forward forms)     *)
(* ================================================================= *)

Lemma NoDup_map_inj : forall (X Y:Type)(f:X->Y)(l:list X),
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros X Y f l; induction l as [|x l IH]; intros Hinj HND; simpl.
  - constructor.
  - inversion HND as [|u v Hnin HND' Heq]; subst.
    constructor.
    + rewrite in_map_iff; intros [y [Hy Hiny]].
      assert (E : x = y) by (apply (Hinj x y); [left; reflexivity | right; exact Hiny | symmetry; exact Hy]).
      rewrite E in Hnin; contradiction.
    + apply IH; [ intros a b Ha Hb; apply Hinj; right; assumption | exact HND' ].
Qed.

Lemma NoDup_list_prod : forall (X Y:Type)(l1:list X)(l2:list Y),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros X Y l1 l2; induction l1 as [|a l1 IH]; intros H1 H2; simpl.
  - constructor.
  - inversion H1 as [|u v Hnin H1' Heq]; subst.
    apply NoDup_app.
    + apply NoDup_map_inj; [ intros p q _ _ E; injection E; auto | exact H2 ].
    + apply IH; [ exact H1' | exact H2 ].
    + intros ab Hin1 Hin2.
      destruct ab as [p q].
      rewrite in_map_iff in Hin1; destruct Hin1 as [y [Ey _]].
      injection Ey as Ep Eq; subst.
      apply in_prod_iff in Hin2; destruct Hin2 as [Hain _]; contradiction.
Qed.

(* ================================================================= *)
(*  §1  free order-4 group action  =>  the length is divisible by 4    *)
(* ================================================================= *)

Section Orbit4.
Context {A : Type}.
Variable eqd : forall x y : A, {x = y} + {x <> y}.
Variable f : A -> A.

(* A NoDup list closed under f, on which f has order dividing 4 and f,   *)
(* f^2 are fixed-point-free, splits into orbits of size exactly 4.      *)
Lemma div4_of_free_order4 : forall L, NoDup L ->
  (forall x, In x L -> In (f x) L) ->
  (forall x, In x L -> f (f (f (f x))) = x) ->
  (forall x, In x L -> f x <> x) ->
  (forall x, In x L -> f (f x) <> x) ->
  Nat.divide 4 (length L).
Proof.
  intro L; induction L as [L IH] using (well_founded_induction (well_founded_ltof _ (@length A))).
  intros HND Hclo Hid Hnf Hnff.
  destruct L as [|a rest].
  - exists 0%nat; reflexivity.
  - pose (x := a).
    assert (Hx_in : In x (a :: rest)) by (left; reflexivity).
    assert (Hfx_in : In (f x) (a :: rest)) by (apply Hclo; exact Hx_in).
    assert (Hffx_in : In (f (f x)) (a :: rest)) by (apply Hclo; exact Hfx_in).
    assert (Hfffx_in : In (f (f (f x))) (a :: rest)) by (apply Hclo; exact Hffx_in).
    assert (finj : forall u v, In u (a::rest) -> In v (a::rest) -> f u = f v -> u = v).
    { intros u v Hu Hv Hf; rewrite <- (Hid u Hu), <- (Hid v Hv), Hf; reflexivity. }
    assert (d_x_fx : x <> f x) by (intro E; exact (Hnf x Hx_in (eq_sym E))).
    assert (d_x_ffx : x <> f (f x)) by (intro E; exact (Hnff x Hx_in (eq_sym E))).
    assert (d_fx_ffx : f x <> f (f x)).
    { intro E; apply d_x_fx; apply (finj x (f x) Hx_in Hfx_in E). }
    assert (d_fx_fffx : f x <> f (f (f x))).
    { intro E; apply d_x_ffx; apply (finj x (f (f x)) Hx_in Hffx_in E). }
    assert (d_ffx_fffx : f (f x) <> f (f (f x))).
    { intro E; apply d_fx_ffx; apply (finj (f x) (f (f x)) Hfx_in Hffx_in E). }
    assert (d_x_fffx : x <> f (f (f x))).
    { intro E; apply (f_equal f) in E; rewrite (Hid x Hx_in) in E;
        apply d_x_fx; symmetry; exact E. }
    set (O := [x; f x; f (f x); f (f (f x))]).
    assert (HO : NoDup O).
    { unfold O.
      apply NoDup_cons. { simpl; intros [E|[E|[E|[]]]];
        [ exact (d_x_fx (eq_sym E)) | exact (d_x_ffx (eq_sym E)) | exact (d_x_fffx (eq_sym E)) ]. }
      apply NoDup_cons. { simpl; intros [E|[E|[]]];
        [ exact (d_fx_ffx (eq_sym E)) | exact (d_fx_fffx (eq_sym E)) ]. }
      apply NoDup_cons. { simpl; intros [E|[]]; exact (d_ffx_fffx (eq_sym E)). }
      apply NoDup_cons. { simpl; intros []. }
      apply NoDup_nil. }
    set (P := fun y => if in_dec eqd y O then true else false).
    assert (inclO : incl O (filter P (a::rest))).
    { intros o Ho; apply filter_In; split.
      - simpl in Ho; destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; assumption.
      - unfold P; destruct (in_dec eqd o O); [ reflexivity | contradiction ]. }
    assert (inclF : incl (filter P (a::rest)) O).
    { intros y Hy; apply filter_In in Hy; destruct Hy as [_ HyP].
      unfold P in HyP; destruct (in_dec eqd y O); [ assumption | discriminate ]. }
    assert (HlenF : length (filter P (a::rest)) = 4%nat).
    { assert (H1 : (4 <= length (filter P (a::rest)))%nat)
        by (change 4%nat with (length O); apply NoDup_incl_length; [ exact HO | exact inclO ]).
      assert (H2 : (length (filter P (a::rest)) <= 4)%nat)
        by (change 4%nat with (length O); apply NoDup_incl_length;
            [ apply NoDup_filter; exact HND | exact inclF ]).
      lia. }
    pose proof (filter_length P (a::rest)) as Hfl.
    assert (Hsplit : (4 + length (filter (fun y => negb (P y)) (a::rest)) = length (a::rest))%nat)
      by (rewrite <- HlenF; exact Hfl).
    assert (subLL : forall y, In y (filter (fun y => negb (P y)) (a::rest)) -> In y (a::rest)).
    { intros y Hy; apply filter_In in Hy; tauto. }
    assert (Hclo' : forall y, In y (filter (fun y => negb (P y)) (a::rest)) ->
                    In (f y) (filter (fun y => negb (P y)) (a::rest))).
    { intros y Hy.
      pose proof (subLL y Hy) as HyL.
      apply filter_In in Hy; destruct Hy as [_ HyP].
      assert (HyO : ~ In y O)
        by (unfold P in HyP; destruct (in_dec eqd y O); [ discriminate | assumption ]).
      assert (HfyL : In (f y) (a::rest)) by (apply Hclo; exact HyL).
      assert (HfyO : ~ In (f y) O).
      { intro Hin; apply HyO; simpl in Hin;
          destruct Hin as [E|[E|[E|[E|[]]]]].
        - assert (Ex : f y = f (f (f (f x)))) by (rewrite (Hid x Hx_in); exact (eq_sym E)).
          pose proof (finj y (f (f (f x))) HyL Hfffx_in Ex) as Hyy.
          simpl; right; right; right; left; exact (eq_sym Hyy).
        - pose proof (finj y x HyL Hx_in (eq_sym E)) as Hyy; simpl; left; exact (eq_sym Hyy).
        - pose proof (finj y (f x) HyL Hfx_in (eq_sym E)) as Hyy; simpl; right; left; exact (eq_sym Hyy).
        - pose proof (finj y (f (f x)) HyL Hffx_in (eq_sym E)) as Hyy;
            simpl; right; right; left; exact (eq_sym Hyy). }
      apply filter_In; split; [ exact HfyL | ].
      unfold P; destruct (in_dec eqd (f y) O); [ contradiction | reflexivity ]. }
    assert (Hlt : (length (filter (fun y => negb (P y)) (a::rest)) < length (a::rest))%nat)
      by lia.
    assert (HND' : NoDup (filter (fun y => negb (P y)) (a::rest)))
      by (apply NoDup_filter; exact HND).
    pose proof (IH (filter (fun y => negb (P y)) (a::rest)) Hlt
                   HND' Hclo'
                   (fun y Hy => Hid y (subLL y Hy))
                   (fun y Hy => Hnf y (subLL y Hy))
                   (fun y Hy => Hnff y (subLL y Hy))) as Hdiv.
    rewrite <- Hsplit.
    apply Nat.divide_add_r; [ exists 1%nat; reflexivity | exact Hdiv ].
Qed.

End Orbit4.

(* ================================================================= *)
(*  §2  the counting function r2 over Z                                *)
(* ================================================================= *)

Open Scope Z_scope.

Definition zzeq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* the Gaussian-unit rotation  (a,b) |-> (-b, a) *)
Definition rot (ab : Z * Z) : Z * Z := (- snd ab, fst ab).

(* the symmetric box  [-s, s]  as an explicit list *)
Definition zbox (s : nat) : list Z :=
  map (fun k => Z.of_nat k - Z.of_nat s) (seq 0 (2 * s + 1)%nat).

Definition boxpairs (s : nat) : list (Z * Z) := list_prod (zbox s) (zbox s).

Definition reps (n : Z) : list (Z * Z) :=
  filter (fun ab => Z.eqb (fst ab * fst ab + snd ab * snd ab) n)
         (boxpairs (Z.to_nat (Z.sqrt n))).

Definition r2 (n : Z) : nat := length (reps n).

(* ----------------------------------------------------------------- *)
(*  box membership and NoDup                                          *)
(* ----------------------------------------------------------------- *)

Lemma zbox_spec : forall s z, In z (zbox s) <-> (- Z.of_nat s <= z <= Z.of_nat s)%Z.
Proof.
  intros s z; unfold zbox; rewrite in_map_iff; split.
  - intros [k [Hk Hin]]; apply in_seq in Hin; subst z; lia.
  - intro Hz; exists (Z.to_nat (z + Z.of_nat s)); split.
    + rewrite Z2Nat.id by lia; ring.
    + apply in_seq.
      assert (0 <= z + Z.of_nat s) by lia.
      assert (z + Z.of_nat s <= 2 * Z.of_nat s) by lia.
      lia.
Qed.

Lemma zbox_NoDup : forall s, NoDup (zbox s).
Proof.
  intro s; unfold zbox; apply NoDup_map_inj; [ intros a b _ _ H; lia | apply seq_NoDup ].
Qed.

Lemma reps_NoDup : forall n, NoDup (reps n).
Proof.
  intro n; unfold reps; apply NoDup_filter; unfold boxpairs;
    apply NoDup_list_prod; apply zbox_NoDup.
Qed.

Lemma reps_In : forall n ab, In ab (reps n) <->
  (In ab (boxpairs (Z.to_nat (Z.sqrt n))) /\ fst ab * fst ab + snd ab * snd ab = n).
Proof.
  intros n ab; unfold reps; rewrite filter_In, Z.eqb_eq; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  §3  positivity of the count  <->  representability                 *)
(* ----------------------------------------------------------------- *)

Lemma r2_pos_iff : forall n, (0 < r2 n)%nat <-> sum2 n.
Proof.
  intro n; unfold r2, sum2; split.
  - intro H; destruct (reps n) as [|ab l] eqn:E; [ simpl in H; lia | ].
    assert (Hin : In ab (reps n)) by (rewrite E; left; reflexivity).
    apply reps_In in Hin; destruct Hin as [_ Heq].
    exists (fst ab), (snd ab); rewrite <- Heq; ring.
  - intros [a [b Hab]].
    assert (Hn0 : 0 <= n) by (rewrite Hab; nia).
    remember (Z.to_nat (Z.sqrt n)) as s eqn:Hs.
    assert (Hsq : Z.of_nat s = Z.sqrt n)
      by (rewrite Hs, Z2Nat.id by apply Z.sqrt_nonneg; reflexivity).
    assert (Hbnd : forall t, t * t <= n -> In t (zbox s)).
    { intros t Ht; apply zbox_spec; rewrite Hsq.
      assert (Habs : Z.abs t * Z.abs t = t * t)
        by (destruct (Z.abs_spec t) as [[_ Ea]|[_ Ea]]; rewrite Ea; ring).
      assert (Hle : Z.abs t <= Z.sqrt n)
        by (apply (proj1 (Z.sqrt_le_square n (Z.abs t) Hn0 (Z.abs_nonneg t)));
            rewrite Habs; exact Ht).
      lia. }
    assert (Ha : In a (zbox s)) by (apply Hbnd; nia).
    assert (Hb : In b (zbox s)) by (apply Hbnd; nia).
    assert (Hin : In (a, b) (reps n)).
    { apply reps_In; split.
      - unfold boxpairs; rewrite <- Hs; apply in_prod_iff; split; [ exact Ha | exact Hb ].
      - simpl; rewrite Hab; ring. }
    destruct (reps n) as [|c l] eqn:E; [ destruct Hin | simpl; lia ].
Qed.

(* full arithmetic characterisation of positivity, via TwoSquaresFull *)
Lemma r2_pos_char : forall n, 0 < n -> ((0 < r2 n)%nat <-> q3even n).
Proof.
  intros n Hn; rewrite (r2_pos_iff n); apply two_squares_iff; exact Hn.
Qed.

(* ----------------------------------------------------------------- *)
(*  §4  the rotation action  =>  4 | r2 n  for n > 0                   *)
(* ----------------------------------------------------------------- *)

Lemma rot4 : forall ab, rot (rot (rot (rot ab))) = ab.
Proof. intros [a b]; unfold rot; cbn [fst snd]; f_equal; ring. Qed.

Lemma rot_closed : forall n ab, In ab (reps n) -> In (rot ab) (reps n).
Proof.
  intros n [a b] Hab.
  apply reps_In in Hab; destruct Hab as [Hbox Heq].
  unfold boxpairs in Hbox; apply in_prod_iff in Hbox; destruct Hbox as [Ha Hb].
  simpl in Heq.
  apply reps_In; split.
  - unfold boxpairs, rot; cbn [fst snd]; apply in_prod_iff; split.
    + apply zbox_spec; apply zbox_spec in Hb; lia.
    + exact Ha.
  - unfold rot; cbn [fst snd]; rewrite <- Heq; ring.
Qed.

Lemma rot_nofix : forall n ab, 0 < n -> In ab (reps n) -> rot ab <> ab.
Proof.
  intros n [a b] Hn Hab E.
  apply reps_In in Hab; destruct Hab as [_ Heq]; simpl in Heq.
  unfold rot in E; cbn [fst snd] in E; injection E as E1 E2.
  assert (Ha0 : a = 0) by lia; assert (Hb0 : b = 0) by lia.
  rewrite Ha0, Hb0 in Heq; lia.
Qed.

Lemma rot2_nofix : forall n ab, 0 < n -> In ab (reps n) -> rot (rot ab) <> ab.
Proof.
  intros n [a b] Hn Hab E.
  apply reps_In in Hab; destruct Hab as [_ Heq]; simpl in Heq.
  unfold rot in E; cbn [fst snd] in E; injection E as E1 E2.
  assert (Ha0 : a = 0) by lia; assert (Hb0 : b = 0) by lia.
  rewrite Ha0, Hb0 in Heq; lia.
Qed.

Lemma r2_div4 : forall n, 0 < n -> Nat.divide 4 (r2 n).
Proof.
  intros n Hn; unfold r2.
  apply (div4_of_free_order4 zzeq_dec rot (reps n)).
  - apply reps_NoDup.
  - intros z Hz; apply rot_closed; exact Hz.
  - intros z _; apply rot4.
  - intros z Hz; apply (rot_nofix n z Hn Hz).
  - intros z Hz; apply (rot2_nofix n z Hn Hz).
Qed.

(* ================================================================= *)
(*  §5  MASTER                                                       *)
(* ================================================================= *)

Theorem two_squares_count :
     (forall n, (0 < r2 n)%nat <-> sum2 n)
  /\ (forall n, 0 < n -> ((0 < r2 n)%nat <-> q3even n))
  /\ (forall n, 0 < n -> Nat.divide 4 (r2 n)).
Proof.
  split; [ exact r2_pos_iff | split; [ exact r2_pos_char | exact r2_div4 ] ].
Qed.

Print Assumptions two_squares_count.

(* ================================================================= *)
(*  END R2Count.v                                                    *)
(*  r2(n) = #{ (a,b) in Z^2 : a^2+b^2 = n } as a bounded decidable     *)
(*  count.  (1) r2(n) > 0  <->  sum2 n  <->  (for n>0) q3even n         *)
(*  (TwoSquaresFull).  (2) 4 | r2(n) for n>0, since the Gaussian-unit   *)
(*  rotation (a,b) |-> (-b,a) is a fixed-point-free order-4 action on   *)
(*  the solution set -- the "4" of Jacobi's r2(n)=4(d1-d3).            *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
