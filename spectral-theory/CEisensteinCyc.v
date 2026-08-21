(* ================================================================= *)
(*  CEisensteinCyc.v  —  the group ring Z[om][x]/(x^p - 1).           *)
(*                                                                    *)
(*    Cyc := nat -> Eis, read only on [0,p)                           *)
(*    cadd, cmul (cyclic convolution), cscale, cpow, Csum, cbar       *)
(*    cdelta / cone / czeta                                           *)
(*    beq p f g := forall u < p, f u = g u                            *)
(*    the ring laws, all stated at beq                                *)
(*                                                                    *)
(*  EQUALITY IS NEVER LEIBNIZ, and that is the one rule the whole     *)
(*  file rests on.  Two functions agreeing on [0,p) are the same      *)
(*  element of the group ring but are not the same term, and proving  *)
(*  them equal would need functional extensionality.  The Eisenstein  *)
(*  tower is axiom-FREE rather than merely axiom-clean, so instead    *)
(*  every law is stated up to beq.  PadicRing.v is the precedent:     *)
(*  function carrier, pointwise relation, hand-rolled congruence      *)
(*  lemmas, no Add Ring.                                              *)
(*                                                                    *)
(*  THIS COSTS NOTHING BECAUSE beq IS POINTWISE.  Each law reduces at *)
(*  a single index to an equation between Eis elements, where the     *)
(*  registered EisRing makes ring fire.  The setoid verbosity that    *)
(*  makes DFTConvolution's conv_theorem_R hard to read comes from an  *)
(*  underlying equality with no pointwise structure; that does not    *)
(*  arise here.                                                       *)
(*                                                                    *)
(*  WHY beq IS SOUND despite saying nothing above p: cmul reads f     *)
(*  only at indices in seq 0 p and g only at msub p n i, which is     *)
(*  always < p.  So a convolution is fully determined by the          *)
(*  restrictions to [0,p) at EVERY index n, not just n < p.  cdelta   *)
(*  is periodic by construction and cmul_per records that convolution *)
(*  outputs are periodic too, which closes the trap where a beq fact  *)
(*  gets used out of range.                                           *)
(*                                                                    *)
(*  ASSOCIATIVITY IS THE ONE REAL PROOF and it is four moves:         *)
(*  distribute h into the inner sum (Esum_scale_r), swap the two sums *)
(*  (Esum_swap), reindex the inner index by j := k + i (Esum_rotate), *)
(*  then normalise with madd_msub_id and msub_madd and pull f i out.  *)
(*  Every index fact it needs was proved in CycIndex, so no mod       *)
(*  arithmetic happens in this file at all.                           *)
(*                                                                    *)
(*  NO PRIMALITY ANYWHERE except Esum_mulperm, which is here only     *)
(*  because the Frobenius step will want it.  The ring itself needs   *)
(*  1 <= p and nothing more.                                          *)
(*  Axiom-free.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation Ring.
Require Import ZmodPStar CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinSum CEisensteinJacobi CEisensteinNormJ
        CycIndex.
Import ListNotations.
Open Scope Z_scope.

(* Esum_opp and econj_invol live inside Sections elsewhere; re-prove *)
Lemma econj_invol : forall z, econj (econj z) = z.
Proof. intros [a b]. unfold econj; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma Esum_opp : forall f l, Esum (fun x => eopp (f x)) l = eopp (Esum f l).
Proof.
  intros f l. induction l as [| x l IH]; [ cbn; unfold Esum; cbn; ring | ].
  rewrite !Esum_cons, IH. ring.
Qed.

Section GroupRing.

Variable p : nat.
Hypothesis Hp1 : (1 <= p)%nat.

(* ----------------------------------------------------------------- *)
(*  A.  three reindexing lemmas over seq 0 p                           *)
(* ----------------------------------------------------------------- *)
Lemma Esum_rotate : forall (F : nat -> Eis) c,
  Esum (fun k => F (madd p k c)) (seq 0 p) = Esum F (seq 0 p).
Proof.
  intros F c. unfold Esum.
  rewrite <- (map_map (fun k => madd p k c) F).
  apply fold_eadd_perm, Permutation_map, rotation_perm. exact Hp1.
Qed.

Lemma Esum_reflect : forall (F : nat -> Eis) n,
  Esum (fun i => F (msub p n i)) (seq 0 p) = Esum F (seq 0 p).
Proof.
  intros F n. unfold Esum.
  rewrite <- (map_map (msub p n) F).
  apply fold_eadd_perm, Permutation_map, reflect_perm. exact Hp1.
Qed.

Lemma Esum_mulperm : prime (Z.of_nat p) -> forall (F : nat -> Eis) m,
  ~ Nat.divide p m ->
  Esum (fun k => F ((m * k) mod p)%nat) (seq 0 p) = Esum F (seq 0 p).
Proof.
  intros Hp F m Hm. unfold Esum.
  rewrite <- (map_map (fun k => (m * k) mod p)%nat F).
  apply fold_eadd_perm, Permutation_map, mulmod_perm0; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the carrier and its operations                                 *)
(* ----------------------------------------------------------------- *)
Definition Cyc := nat -> Eis.

Definition czero : Cyc := fun _ => ezero.
Definition cdelta (a : nat) : Cyc :=
  fun u => if Nat.eqb (u mod p) (a mod p) then eone else ezero.
Definition cone : Cyc := cdelta 0.
Definition czeta : Cyc := cdelta 1.
Definition cadd (f g : Cyc) : Cyc := fun u => eadd (f u) (g u).
Definition copp (f : Cyc) : Cyc := fun u => eopp (f u).
Definition csub (f g : Cyc) : Cyc := fun u => esub (f u) (g u).
Definition cscale (c : Eis) (f : Cyc) : Cyc := fun u => emul c (f u).
Definition cbar (f : Cyc) : Cyc := fun u => econj (f u).
Definition cmul (f g : Cyc) : Cyc :=
  fun n => Esum (fun i => emul (f i) (g (msub p n i))) (seq 0 p).
Fixpoint cpow (f : Cyc) (k : nat) : Cyc :=
  match k with O => cone | S j => cmul f (cpow f j) end.
Definition cemb (c : Eis) : Cyc := cscale c cone.
Definition Csum (F : nat -> Cyc) (l : list nat) : Cyc :=
  fun u => Esum (fun k => F k u) l.

Definition beq (f g : Cyc) : Prop := forall u, (u < p)%nat -> f u = g u.

(* ----------------------------------------------------------------- *)
(*  C.  beq is an equivalence, and a congruence                        *)
(* ----------------------------------------------------------------- *)
Lemma beq_refl : forall f, beq f f.
Proof. intros f u _. reflexivity. Qed.

Lemma beq_sym : forall f g, beq f g -> beq g f.
Proof. intros f g H u Hu. symmetry. apply H. exact Hu. Qed.

Lemma beq_trans : forall f g h, beq f g -> beq g h -> beq f h.
Proof. intros f g h H1 H2 u Hu. rewrite H1 by exact Hu. apply H2. exact Hu. Qed.

Lemma beq_cadd : forall f f' g g', beq f f' -> beq g g' -> beq (cadd f g) (cadd f' g').
Proof.
  intros f f' g g' H1 H2 u Hu. unfold cadd.
  rewrite H1, H2 by exact Hu. reflexivity.
Qed.

Lemma beq_copp : forall f f', beq f f' -> beq (copp f) (copp f').
Proof. intros f f' H u Hu. unfold copp. rewrite H by exact Hu. reflexivity. Qed.

Lemma beq_cscale : forall c f f', beq f f' -> beq (cscale c f) (cscale c f').
Proof. intros c f f' H u Hu. unfold cscale. rewrite H by exact Hu. reflexivity. Qed.

Lemma beq_cbar : forall f f', beq f f' -> beq (cbar f) (cbar f').
Proof. intros f f' H u Hu. unfold cbar. rewrite H by exact Hu. reflexivity. Qed.

(* the crux: cmul reads its arguments only below p *)
Lemma beq_cmul : forall f f' g g', beq f f' -> beq g g' -> beq (cmul f g) (cmul f' g').
Proof.
  intros f f' g g' H1 H2 n Hn. unfold cmul.
  apply Esum_ext. intros i Hi. apply in_seq in Hi.
  rewrite H1 by lia. rewrite H2 by (apply msub_lt; exact Hp1). reflexivity.
Qed.

Lemma beq_cpow : forall f f' k, beq f f' -> beq (cpow f k) (cpow f' k).
Proof.
  intros f f' k H. induction k as [| k IH]; cbn [cpow].
  - apply beq_refl.
  - apply beq_cmul; assumption.
Qed.

Lemma beq_Csum : forall F G l,
  (forall k, In k l -> beq (F k) (G k)) -> beq (Csum F l) (Csum G l).
Proof.
  intros F G l H u Hu. unfold Csum. apply Esum_ext.
  intros k Hk. apply H; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the additive group                                             *)
(* ----------------------------------------------------------------- *)
Lemma cadd_comm : forall f g, beq (cadd f g) (cadd g f).
Proof. intros f g u _. unfold cadd. ring. Qed.

Lemma cadd_assoc : forall f g h, beq (cadd (cadd f g) h) (cadd f (cadd g h)).
Proof. intros f g h u _. unfold cadd. ring. Qed.

Lemma cadd_0_l : forall f, beq (cadd czero f) f.
Proof. intros f u _. unfold cadd, czero. ring. Qed.

Lemma cadd_opp : forall f, beq (cadd f (copp f)) czero.
Proof. intros f u _. unfold cadd, copp, czero. ring. Qed.

Lemma csub_spec : forall f g, beq (csub f g) (cadd f (copp g)).
Proof. intros f g u _. unfold csub, cadd, copp, esub. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the multiplication                                             *)
(* ----------------------------------------------------------------- *)
Lemma cmul_per : forall f g n, cmul f g n = cmul f g (n mod p)%nat.
Proof.
  intros f g n. unfold cmul. apply Esum_ext. intros i Hi. apply in_seq in Hi.
  rewrite (msub_per p Hp1 n i ltac:(lia)). reflexivity.
Qed.

Lemma cmul_0_l : forall f, beq (cmul czero f) czero.
Proof.
  intros f n _. unfold cmul, czero. apply Esum_zero_ext.
  intros i _. ring.
Qed.

Lemma cmul_comm : forall f g, beq (cmul f g) (cmul g f).
Proof.
  intros f g n Hn. unfold cmul.
  rewrite <- (Esum_reflect (fun i => emul (f i) (g (msub p n i))) n).
  apply Esum_ext. intros i Hi. apply in_seq in Hi.
  rewrite (msub_invol p Hp1 n i ltac:(lia)). ring.
Qed.

Lemma cmul_distr_l : forall f g h,
  beq (cmul f (cadd g h)) (cadd (cmul f g) (cmul f h)).
Proof.
  intros f g h n _. unfold cmul, cadd.
  rewrite <- Esum_add. apply Esum_ext. intros i _. ring.
Qed.

Lemma cmul_assoc : forall f g h, beq (cmul (cmul f g) h) (cmul f (cmul g h)).
Proof.
  intros f g h n Hn. unfold cmul at 1 3.
  (* 1. distribute h into the inner sum *)
  rewrite (Esum_ext _ (fun j => Esum (fun i =>
              emul (emul (f i) (g (msub p j i))) (h (msub p n j))) (seq 0 p))
              (seq 0 p)).
  2:{ intros j _. unfold cmul. symmetry.
      exact (Esum_scale_r (h (msub p n j))
               (fun i => emul (f i) (g (msub p j i))) (seq 0 p)). }
  (* 2. swap *)
  rewrite Esum_swap.
  (* 3+4. reindex the inner sum and normalise *)
  apply Esum_ext. intros i Hi. apply in_seq in Hi.
  rewrite <- (Esum_rotate (fun j =>
      emul (emul (f i) (g (msub p j i))) (h (msub p n j))) i).
  unfold cmul.
  rewrite <- (Esum_scale_l (f i)
      (fun k => emul (g k) (h (msub p (msub p n i) k))) (seq 0 p)).
  apply Esum_ext. intros k Hk. apply in_seq in Hk.
  rewrite (madd_msub_id p Hp1 k i ltac:(lia) ltac:(lia)).
  rewrite (msub_madd p Hp1 n k i ltac:(lia) ltac:(lia)).
  ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  deltas, the unit, and zeta                                     *)
(* ----------------------------------------------------------------- *)
Lemma cdelta_hit : forall a, cdelta a a = eone.
Proof. intro a. unfold cdelta. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma cdelta_miss : forall a x, (a < p)%nat -> (x < p)%nat -> x <> a ->
  cdelta a x = ezero.
Proof.
  intros a x Ha Hx Hne. unfold cdelta.
  rewrite (Nat.mod_small x p) by lia. rewrite (Nat.mod_small a p) by lia.
  destruct (Nat.eqb_spec x a); [ contradiction | reflexivity ].
Qed.

Theorem cmul_delta_l : forall a f, (a < p)%nat ->
  beq (cmul (cdelta a) f) (fun n => f (msub p n a)).
Proof.
  intros a f Ha n Hn. unfold cmul.
  rewrite (Esum_del (fun i => emul (cdelta a i) (f (msub p n i))) a (seq 0 p)
             (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  rewrite cdelta_hit.
  assert (Hz : Esum (fun i => emul (cdelta a i) (f (msub p n i)))
                    (del a (seq 0 p)) = ezero).
  { apply Esum_zero_ext. intros x Hx.
    apply In_del in Hx as [Hin Hne]. apply in_seq in Hin.
    rewrite (cdelta_miss a x Ha ltac:(lia) Hne). ring. }
  rewrite Hz. ring.
Qed.

Corollary cmul_1_l : forall f, beq (cmul cone f) f.
Proof.
  intros f n Hn. unfold cone.
  rewrite (cmul_delta_l 0 f ltac:(lia) n Hn).
  rewrite (msub_small p Hp1 n Hn). reflexivity.
Qed.

Corollary cmul_1_r : forall f, beq (cmul f cone) f.
Proof.
  intro f. apply (beq_trans _ (cmul cone f)); [ apply cmul_comm | apply cmul_1_l ].
Qed.

(* zeta really is a p-th root of unity: zeta^k = delta_{k mod p}.
   Not needed by anything downstream, but without it nothing in this
   file distinguishes the construction from a degenerate one. *)
Lemma msub1_iff : (2 <= p)%nat -> forall n k, (n < p)%nat ->
  (msub p n 1 = (k mod p)%nat <-> n = (S k mod p)%nat).
Proof.
  intros Hp2 n k Hn.
  destruct (msub_cg p Hp1 n 1 ltac:(lia)) as [a Ha].
  destruct (cgp_mod p Hp1 (S k)) as [b Hb].
  destruct (cgp_mod p Hp1 k) as [c Hc].
  split.
  - intro Hmk. apply (cgp_eq p Hp1); [ lia | apply Nat.mod_upper_bound; lia | ].
    rewrite Hmk in Ha. exists (c - a - b). lia.
  - intro Hn2. apply (cgp_eq p Hp1);
      [ apply msub_lt; exact Hp1 | apply Nat.mod_upper_bound; lia | ].
    rewrite <- Hn2 in Hb. exists (a + b - c). lia.
Qed.

Theorem cpow_czeta : (2 <= p)%nat -> forall k,
  beq (cpow czeta k) (cdelta (k mod p)).
Proof.
  intros Hp2 k. induction k as [| k IH].
  - rewrite Nat.Div0.mod_0_l. apply beq_refl.
  - apply (beq_trans _ (cmul (cdelta 1) (cdelta (k mod p)))).
    { cbn [cpow]. apply beq_cmul; [ apply beq_refl | exact IH ]. }
    apply (beq_trans _ (fun n => cdelta (k mod p) (msub p n 1)));
      [ apply cmul_delta_l; lia | ].
    intros n Hn. cbn beta. unfold cdelta.
    rewrite (Nat.mod_small (msub p n 1) p) by (apply msub_lt; exact Hp1).
    rewrite (Nat.mod_small n p) by lia.
    rewrite !Nat.Div0.mod_mod.
    destruct (Nat.eqb_spec (msub p n 1) (k mod p)) as [E1 | E1];
    destruct (Nat.eqb_spec n (S k mod p)) as [E2 | E2]; try reflexivity.
    + exfalso. apply E2. apply (msub1_iff Hp2 n k Hn). exact E1.
    + exfalso. apply E1. apply (msub1_iff Hp2 n k Hn). exact E2.
Qed.

(* ----------------------------------------------------------------- *)
(*  G.  scalars                                                        *)
(* ----------------------------------------------------------------- *)
Lemma cscale_cmul : forall c f, beq (cscale c f) (cmul (cemb c) f).
Proof.
  intros c f n Hn. unfold cemb.
  (* cemb c = cscale c cone = fun u => emul c (cone u) *)
  unfold cmul, cscale, cone.
  rewrite (Esum_del (fun i => emul (emul c (cdelta 0 i)) (f (msub p n i)))
             0%nat (seq 0 p) (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  rewrite cdelta_hit.
  assert (Hz : Esum (fun i => emul (emul c (cdelta 0 i)) (f (msub p n i)))
                    (del 0 (seq 0 p)) = ezero).
  { apply Esum_zero_ext. intros x Hx.
    apply In_del in Hx as [Hin Hne]. apply in_seq in Hin.
    rewrite (cdelta_miss 0 x ltac:(lia) ltac:(lia) Hne). ring. }
  rewrite Hz, (msub_small p Hp1 n Hn). ring.
Qed.

Lemma cscale_cmul_assoc : forall c f g, beq (cscale c (cmul f g)) (cmul (cscale c f) g).
Proof.
  intros c f g n _. unfold cscale, cmul.
  rewrite <- (Esum_scale_l c (fun i => emul (f i) (g (msub p n i))) (seq 0 p)).
  apply Esum_ext. intros i _. ring.
Qed.

Lemma cemb_add : forall a b, beq (cemb (eadd a b)) (cadd (cemb a) (cemb b)).
Proof. intros a b u _. unfold cemb, cscale, cadd. ring. Qed.

(* ----------------------------------------------------------------- *)
(*  H.  coefficientwise conjugation is a ring map                      *)
(* ----------------------------------------------------------------- *)
Lemma cbar_add : forall f g, beq (cbar (cadd f g)) (cadd (cbar f) (cbar g)).
Proof. intros f g u _. unfold cbar, cadd. apply econj_add. Qed.

Lemma cbar_invol : forall f, beq (cbar (cbar f)) f.
Proof. intros f u _. unfold cbar. apply econj_invol. Qed.

Lemma cbar_mul : forall f g, beq (cbar (cmul f g)) (cmul (cbar f) (cbar g)).
Proof.
  intros f g n _. unfold cbar, cmul.
  rewrite econj_Esum. apply Esum_ext. intros i _. apply econj_mul.
Qed.

End GroupRing.

Print Assumptions cmul_assoc.
Print Assumptions cmul_comm.
Print Assumptions cmul_1_l.
Print Assumptions cbar_mul.
Print Assumptions cpow_czeta.
