(* ================================================================= *)
(*  PrimorialTensorGen.v  —  Brick 5, general case: the CRT monoid       *)
(*  isomorphism  M_{mn} ~= M_m x M_n  for ANY coprime m, n (over nat),   *)
(*  generalizing PrimorialMonoidAlgebra's vm_compute-at-6 crt_monoid_iso.*)
(*                                                                    *)
(*  M_k = (Z/k, x) is the residue multiplicative monoid; crt : x |->     *)
(*  (x mod m, x mod n) carries mult-mod-mn to componentwise mult, and is *)
(*  a bijection of residue systems (CRT).  Composed with the already-     *)
(*  generic HopfGroupTensor.gconv_prod_tensor this gives the algebra      *)
(*  tensor  Z[M_{mn}] ~= Z[M_m] (x) Z[M_n]; iterating over the primes of  *)
(*  a primorial gives the k-fold factorization.  Axiom-free.            *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia PeanoNat List Permutation ZArith Znumtheory.
Require Import ProfiniteCRT HopfGroupTensor.
Import ListNotations.
Open Scope nat_scope.

(* sumf respects permutations (Z addition is commutative/associative) *)
Lemma sumf_perm {A} : forall (l l' : list A) (F : A -> Z),
  Permutation l l' -> sumf l F = sumf l' F.
Proof.
  intros l l' F Hp; unfold sumf; induction Hp; simpl.
  - reflexivity.
  - rewrite IHHp; reflexivity.
  - lia.
  - rewrite IHHp1, IHHp2; reflexivity.
Qed.

(* NoDup of a map under injectivity ON the list (local, not global) *)
Lemma nodup_map_local {A B} : forall (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros f l Hinj Hnd; induction l as [|a l IH]; simpl; [ constructor | ].
  inversion Hnd as [|x xs Hna Hnd']; subst. constructor.
  - intro Hin; apply in_map_iff in Hin as [b [Hfb Hb]].
    apply Hna. rewrite (Hinj a b (or_introl eq_refl) (or_intror Hb) (eq_sym Hfb)). exact Hb.
  - apply IH; [ intros x y Hx Hy Hf; apply (Hinj x y (or_intror Hx) (or_intror Hy) Hf)
              | exact Hnd' ].
Qed.

Section GenCRT.
Variables m n : nat.
Hypothesis Hm : 0 < m.
Hypothesis Hn : 0 < n.
Hypothesis Hcop : rel_prime (Z.of_nat m) (Z.of_nat n).

(* the three monoid operations and the CRT map *)
Definition opm (x y : nat) : nat := (x * y) mod m.
Definition opn (x y : nat) : nat := (x * y) mod n.
Definition opmn (x y : nat) : nat := (x * y) mod (m * n).
Definition crt (x : nat) : nat * nat := (x mod m, x mod n).
Definition cop (p q : nat * nat) : nat * nat :=
  (opm (fst p) (fst q), opn (snd p) (snd q)).

Definition em : list nat := seq 0 m.
Definition en : list nat := seq 0 n.
Definition emn : list nat := seq 0 (m * n).
Definition eAB : list (nat * nat) := list_prod em en.

(* (a mod (m*n)) mod m = a mod m  and the n-analogue *)
Lemma modmod_l : forall a, (a mod (m * n)) mod m = a mod m.
Proof.
  intro a. rewrite Nat.Div0.mod_mul_r, (Nat.mul_comm m ((a / m) mod n)),
    Nat.Div0.mod_add, Nat.Div0.mod_mod; reflexivity.
Qed.

Lemma modmod_r : forall a, (a mod (m * n)) mod n = a mod n.
Proof.
  intro a. rewrite (Nat.mul_comm m n), Nat.Div0.mod_mul_r,
    (Nat.mul_comm n ((a / n) mod m)), Nat.Div0.mod_add, Nat.Div0.mod_mod; reflexivity.
Qed.

(* ---- crt is a monoid homomorphism (all x, y) ---- *)
Theorem crt_hom : forall x y, crt (opmn x y) = cop (crt x) (crt y).
Proof.
  intros x y; unfold crt, cop, opmn, opm, opn; simpl; f_equal.
  - rewrite modmod_l, Nat.Div0.mul_mod; reflexivity.
  - rewrite modmod_r, Nat.Div0.mul_mod; reflexivity.
Qed.

(* ---- crt is injective on [0, m*n) (CRT injectivity, via Z) ---- *)
Theorem crt_inj : forall x y, x < m * n -> y < m * n -> crt x = crt y -> x = y.
Proof.
  intros x y Hx Hy Heq; unfold crt in Heq; injection Heq as Hem Hen.
  apply Nat2Z.inj.
  assert (Hdm : (Z.of_nat m | Z.of_nat x - Z.of_nat y)%Z).
  { apply sub_of_mod_eq; [ lia | rewrite <- !Nat2Z.inj_mod, Hem; reflexivity ]. }
  assert (Hdn : (Z.of_nat n | Z.of_nat x - Z.of_nat y)%Z).
  { apply sub_of_mod_eq; [ lia | rewrite <- !Nat2Z.inj_mod, Hen; reflexivity ]. }
  assert (Hdmn : (Z.of_nat m * Z.of_nat n | Z.of_nat x - Z.of_nat y)%Z)
    by (apply mul_divide_of_coprime; assumption).
  destruct (Z.eq_dec (Z.of_nat x - Z.of_nat y) 0) as [H0 | Hne]; [ lia | exfalso ].
  assert (Hle : (Z.of_nat m * Z.of_nat n <= Z.abs (Z.of_nat x - Z.of_nat y))%Z)
    by (apply Z.divide_pos_le;
        [ apply Z.abs_pos; exact Hne | apply Z.divide_abs_r; exact Hdmn ]).
  assert (Hmn : (Z.of_nat m * Z.of_nat n)%Z = Z.of_nat (m * n)) by (rewrite Nat2Z.inj_mul; reflexivity).
  lia.
Qed.

(* ---- crt is a bijection of residue systems:  emn <~> eAB ---- *)
Lemma crt_incl : incl (map crt emn) eAB.
Proof.
  intros p Hp. apply in_map_iff in Hp as [x [Hx Hxin]]. subst p.
  unfold emn in Hxin; apply in_seq in Hxin.
  apply in_prod; unfold em, en, crt; simpl; apply in_seq; split; try lia.
  - apply Nat.mod_upper_bound; lia.
  - apply Nat.mod_upper_bound; lia.
Qed.

Lemma len_emn : length emn = m * n.
Proof. unfold emn; apply length_seq. Qed.

Lemma len_eAB : length eAB = m * n.
Proof. unfold eAB, em, en; rewrite length_prod, !length_seq; reflexivity. Qed.

Lemma nodup_map_crt : NoDup (map crt emn).
Proof.
  apply nodup_map_local; [ | apply seq_NoDup ].
  intros x y Hx Hy; unfold emn in Hx, Hy; apply in_seq in Hx, Hy.
  apply crt_inj; lia.
Qed.

Lemma crt_perm : Permutation (map crt emn) eAB.
Proof.
  apply NoDup_Permutation_bis;
    [ apply nodup_map_crt
    | rewrite length_map, len_emn, len_eAB; lia
    | apply crt_incl ].
Qed.

(* THE general reindexing:  a grid sum = a residue sum, transported by crt *)
Theorem sumf_reindex_crt : forall (G : nat * nat -> Z),
  sumf eAB G = sumf emn (fun x => G (crt x)).
Proof.
  intro G. rewrite (sumf_perm _ _ G (Permutation_sym crt_perm)).
  apply sumf_map.
Qed.

(* ---- the general CRT monoid isomorphism  M_{mn} ~= M_m x M_n ---- *)
Theorem crt_monoid_iso_gen :
  (forall x y, crt (opmn x y) = cop (crt x) (crt y))          (* homomorphism *)
  /\ (forall x y, x < m * n -> y < m * n -> crt x = crt y -> x = y)  (* injective *)
  /\ Permutation (map crt emn) eAB.                            (* bijective reindex *)
Proof. split; [ exact crt_hom | split; [ exact crt_inj | exact crt_perm ] ]. Qed.

(* ---- MASTER THEOREM (general coprime m, n):  Z[M_{mn}] ~= Z[M_m] (x) Z[M_n] ----
   (1) the CRT monoid iso M_{mn} ~= M_m x M_n, and (2) the generic algebra
   tensor Z[M_m x M_n] ~= Z[M_m] (x) Z[M_n] (currying = HopfGroupTensor).
   This is PrimorialMonoidAlgebra.primorial_tensor_factorization with the
   216-case vm_compute replaced by a proof valid for every coprime m, n. *)
Theorem primorial_tensor_factorization_gen :
  ( (forall x y, crt (opmn x y) = cop (crt x) (crt y))
    /\ (forall x y, x < m * n -> y < m * n -> crt x = crt y -> x = y)
    /\ Permutation (map crt emn) eAB )
  /\ (forall (f f' : nat * nat -> Z) (g h : nat),
        gconvGH Nat.eqb Nat.eqb em en opm opn f f' (g, h)
        = tconv Nat.eqb Nat.eqb em en opm opn
            (fun a b => f (a, b)) (fun a b => f' (a, b)) g h).
Proof.
  split; [ exact crt_monoid_iso_gen | intros f f' g h; apply gconv_prod_tensor ].
Qed.

End GenCRT.

Print Assumptions primorial_tensor_factorization_gen.

Print Assumptions crt_monoid_iso_gen.
Print Assumptions sumf_reindex_crt.

