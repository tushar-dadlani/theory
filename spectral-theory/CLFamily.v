(* ================================================================= *)
(*  CLFamily.v  --  the family really is infinite.                    *)
(*                                                                    *)
(*  A theorem about "infinitely many L-functions" that was secretly    *)
(*  about one function would typecheck and say nothing.  Two checks:   *)
(*                                                                    *)
(*   (1) the p-1 characters mod p are PAIRWISE DISTINCT -- they take   *)
(*       distinct values at the primitive root g, because w (p-1) is   *)
(*       a primitive (p-1)-th root of unity (RootsOfUnity.w_primitive).*)
(*       Hence the p-1 coefficient sequences chi(n) n^{-s}, and so the *)
(*       p-1 L-series, are pairwise distinct objects.                  *)
(*                                                                    *)
(*   (2) there are infinitely many moduli, from DirichletAP's          *)
(*       cyclotomic proof at n = 1.                                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory.
Require Import ComplexField Cmodulus RootsOfUnity CharactersModN
        ZmodOrder DirichletModP CharModulus DirichletAP.
Open Scope R_scope.

Lemma Cpow_w_ne0 : forall N k, Cpow (w N) k <> C0.
Proof.
  intros N k Hk.
  pose proof (Cmod_Cpow_loc (w N) k) as Hm.
  rewrite Hk, (proj2 (Cmod0 C0) eq_refl), Cmod_w, pow1 in Hm. lra.
Qed.

(* the powers of a primitive N-th root of unity are distinct below N *)
Lemma Cpow_w_inj : forall N u v, (u < N)%nat -> (v < N)%nat ->
  Cpow (w N) u = Cpow (w N) v -> u = v.
Proof.
  intros N u v Hu Hv He.
  destruct (Nat.lt_trichotomy u v) as [H | [H | H]]; [ exfalso | exact H | exfalso ].
  - assert (Hd : (v = u + (v - u))%nat) by lia.
    rewrite Hd, Cpow_add in He.
    assert (Hc : Cpow (w N) (v - u) = C1).
    { pose proof (Cpow_w_ne0 N u) as Hu0.
      replace (Cpow (w N) (v - u))
        with (Cmul (Cinv (Cpow (w N) u))
                   (Cmul (Cpow (w N) u) (Cpow (w N) (v - u))))
        by (field; exact Hu0).
      rewrite <- He. field; exact Hu0. }
    apply (w_primitive N (v - u) ltac:(lia)); exact Hc.
  - assert (Hd : (u = v + (u - v))%nat) by lia.
    rewrite Hd, Cpow_add in He.
    assert (Hc : Cpow (w N) (u - v) = C1).
    { pose proof (Cpow_w_ne0 N v) as Hv0.
      replace (Cpow (w N) (u - v))
        with (Cmul (Cinv (Cpow (w N) v))
                   (Cmul (Cpow (w N) v) (Cpow (w N) (u - v))))
        by (field; exact Hv0).
      rewrite He. field; exact Hv0. }
    apply (w_primitive N (u - v) ltac:(lia)); exact Hc.
Qed.

(* THE p-1 CHARACTERS MOD p ARE PAIRWISE DISTINCT *)
Theorem dchar_distinct : forall p g u v,
  prime (Z.of_nat p) -> (1 <= g <= p - 1)%nat -> ord p g = (p - 1)%nat ->
  (u < p - 1)%nat -> (v < p - 1)%nat -> u <> v ->
  dchar p g u (pw p g 1) <> dchar p g v (pw p g 1).
Proof.
  intros p g u v Hp Hg Hord Hu Hv Huv Heq.
  rewrite (dchar_on_power p g u 1 Hp Hg Hord ltac:(lia)) in Heq.
  rewrite (dchar_on_power p g v 1 Hp Hg Hord ltac:(lia)) in Heq.
  unfold chi in Heq. rewrite !Nat.mul_1_r in Heq.
  exact (Huv (Cpow_w_inj (p - 1) u v Hu Hv Heq)).
Qed.

(* THERE ARE INFINITELY MANY MODULI *)
Theorem infinitely_many_moduli : forall B,
  exists q, prime (Z.of_nat q) /\ (B < q)%nat.
Proof.
  intro B.
  destruct (dirichlet_primes_1_mod_n 1 ltac:(lia) B) as [q [Hq [HB _]]].
  exists q; split; assumption.
Qed.

Print Assumptions dchar_distinct.
Print Assumptions infinitely_many_moduli.

(* ================================================================= *)
(*  END CLFamily.v                                                    *)
(* ================================================================= *)
