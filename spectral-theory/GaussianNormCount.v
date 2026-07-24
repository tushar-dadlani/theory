(* ================================================================= *)
(*  GaussianNormCount.v                                              *)
(*                                                                    *)
(*  r2(n) AS A Z[i] NORM-COUNT -- the bridge from the lattice-point   *)
(*  count r2 (R2Count) to counting Gaussian integers of norm n, so    *)
(*  the Z[i] unique-factorisation machinery can be brought to bear    *)
(*  on the general Jacobi identity r2(n) = 4 * S(n).                  *)
(*                                                                    *)
(*      r2(n) = #{ z in Z[i] : N(z) = n }.                           *)
(*                                                                    *)
(*  R2Count.r2 already counts integer pairs (a,b) with a^2+b^2 = n;    *)
(*  under (a,b) <-> a+bi this is exactly the Gaussian integers of      *)
(*  norm n in the same box, so the two counts coincide.  AXIOM-FREE.  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Arith List Bool.
Require Import GaussianIntegers GaussianFactorization R2Count.
Import ListNotations.
Open Scope Z_scope.

Lemma length_filter_map : forall (A B : Type) (f : A -> B) (g : B -> bool) (l : list A),
  length (filter g (map f l)) = length (filter (fun a => g (f a)) l).
Proof.
  intros A B f g l; induction l as [|a l IH]; simpl; [ reflexivity | ].
  destruct (g (f a)); simpl; rewrite IH; reflexivity.
Qed.

(* r2(n) equals the number of Gaussian integers of norm n in the box. *)
Theorem r2_as_gnorm : forall n,
  r2 n = length (filter (fun z => ZInorm (-1) z =? n)
                        (gbox (Z.to_nat (Z.sqrt n)))).
Proof.
  intro n; unfold r2, reps, boxpairs.
  assert (Hz : R2Count.zbox = zrange) by reflexivity.
  rewrite Hz; unfold gbox; rewrite length_filter_map.
  f_equal; apply filter_ext_in; intros ab _.
  assert (H : (fst ab * fst ab + snd ab * snd ab)
              = ZInorm (-1) (mkZI (fst ab) (snd ab)))
    by (unfold ZInorm; cbn [zRe zIm]; ring).
  rewrite H; reflexivity.
Qed.

Print Assumptions r2_as_gnorm.

(* ================================================================= *)
(*  END GaussianNormCount.v (part 1: the bridge)                     *)
(*  r2(n) = #{z : N(z)=n}: R2Count's lattice count re-read in Z[i].   *)
(*  Foundation for counting norm-n elements via unique factorisation. *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
