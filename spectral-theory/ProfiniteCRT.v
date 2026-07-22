(* ================================================================= *)
(*  ProfiniteCRT.v                                                   *)
(*                                                                    *)
(*  THE PROFINITE SIDE MADE EXPLICIT.                                 *)
(*                                                                    *)
(*  The profinite completion of Z is the inverse limit                *)
(*        Zhat  =  lim_n  Z/nZ   (over n ordered by divisibility)      *)
(*  and by CRT it factors as the product over primes                  *)
(*        Zhat  =  prod_p  Z_p ,   Z_p = lim_k Z/p^k Z .               *)
(*  This is the FINITE / non-archimedean factor of the adele ring      *)
(*  A_Q = R x A_f  (ProductFormulaQ) -- and, unlike R, it is built     *)
(*  entirely from finite discrete data, hence AXIOM-FREE.  Here we      *)
(*  make its two defining ingredients explicit and machine-checked:    *)
(*                                                                    *)
(*  (1) THE CRT RING ISOMORPHISM  Z/mnZ  ~=  Z/mZ x Z/nZ  (coprime      *)
(*      m,n): the reduction pair  x |-> (x mod m, x mod n)  is a        *)
(*      bijection with explicit Bezout reconstruction (crt_iso), and   *)
(*      reduction is a ring homomorphism (Zplus_mod / Zmult_mod).      *)
(*      Iterating over n = prod_p p^{v_p(n)} gives the finite shadow    *)
(*      Z/nZ ~= prod_p Z/p^{v_p} Z  of  Zhat ~= prod_p Z_p.            *)
(*                                                                    *)
(*  (2) THE INVERSE SYSTEM  lim_n Z/nZ: the projection maps            *)
(*      pi : Z/nZ -> Z/dZ (reduction, for d | n) COMMUTE with the       *)
(*      tower (proj_compat: (x mod n) mod d = x mod d), the             *)
(*      prime-power tower Z/p^{k+1} -> Z/p^k is an instance             *)
(*      (tower_proj), and the index set is directed (system_directed:   *)
(*      any two levels divide their product).  A cofiltered inverse     *)
(*      system of finite rings -- exactly the data of Zhat.            *)
(*                                                                    *)
(*  Axiom-free: constructive Z arithmetic + Znumtheory Bezout/Gauss     *)
(*  (Closed under the global context).                               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  Congruence <-> divisibility plumbing                             *)
(* ----------------------------------------------------------------- *)

Lemma mod_eq_sub : forall n a b, n <> 0 -> (n | a - b) -> a mod n = b mod n.
Proof.
  intros n a b Hn [k Hk].
  replace a with (b + k * n) by lia.
  apply Z.mod_add; exact Hn.
Qed.

Lemma sub_of_mod_eq : forall n a b, n <> 0 -> a mod n = b mod n -> (n | a - b).
Proof.
  intros n a b Hn H.
  exists (a / n - b / n).
  pose proof (Z.mod_eq a n Hn) as Ha.
  pose proof (Z.mod_eq b n Hn) as Hb.
  nia.
Qed.

(* two coprime divisors of k have their product divide k *)
Lemma mul_divide_of_coprime : forall m n k,
  rel_prime m n -> (m | k) -> (n | k) -> (m * n | k).
Proof.
  intros m n k Hcop [k1 Hk1] Hnk.
  assert (Hn_mk1 : (n | m * k1))
    by (replace (m * k1) with k by (rewrite Hk1; ring); exact Hnk).
  destruct (Gauss n m k1 Hn_mk1 (rel_prime_sym m n Hcop)) as [k2 Hk2].
  exists k2; rewrite Hk1, Hk2; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  (1) THE CRT RING ISOMORPHISM  Z/mnZ ~= Z/mZ x Z/nZ               *)
(*                                                                    *)
(*  Given a Bezout witness  u*m + v*n = 1,  the reconstruction        *)
(*     recon a b = a*(v*n) + b*(u*m)                                  *)
(*  inverts the reduction pair:  v*n = 1 (mod m), 0 (mod n) and        *)
(*  u*m = 0 (mod m), 1 (mod n), so recon a b = a (mod m) = b (mod n).  *)
(* ----------------------------------------------------------------- *)

Definition recon (u v m n a b : Z) : Z := a * (v * n) + b * (u * m).

Lemma crt_proj_m : forall u v m n a b, u * m + v * n = 1 -> m <> 0 ->
  (recon u v m n a b) mod m = a mod m.
Proof.
  intros u v m n a b Hbez Hm.
  apply mod_eq_sub; [ exact Hm | ].
  exists (u * (b - a)).
  assert (Hvn : v * n = 1 - u * m) by lia.
  unfold recon; rewrite Hvn; ring.
Qed.

Lemma crt_proj_n : forall u v m n a b, u * m + v * n = 1 -> n <> 0 ->
  (recon u v m n a b) mod n = b mod n.
Proof.
  intros u v m n a b Hbez Hn.
  apply mod_eq_sub; [ exact Hn | ].
  exists (v * (a - b)).
  assert (Hum : u * m = 1 - v * n) by lia.
  unfold recon; rewrite Hum; ring.
Qed.

(* the reconstruction of a genuine x recovers x mod (m*n) *)
Lemma crt_roundtrip : forall u v m n x, 0 < m -> 0 < n -> rel_prime m n ->
  u * m + v * n = 1 ->
  (recon u v m n (x mod m) (x mod n)) mod (m * n) = x mod (m * n).
Proof.
  intros u v m n x Hm Hn Hcop Hbez.
  apply mod_eq_sub; [ nia | ].
  apply mul_divide_of_coprime; [ exact Hcop | | ].
  - apply sub_of_mod_eq; [ lia | ].
    rewrite (crt_proj_m u v m n (x mod m) (x mod n) Hbez ltac:(lia)).
    apply Zmod_mod.
  - apply sub_of_mod_eq; [ lia | ].
    rewrite (crt_proj_n u v m n (x mod m) (x mod n) Hbez ltac:(lia)).
    apply Zmod_mod.
Qed.

(* THE CRT ISOMORPHISM: the reduction pair is a bijection with        *)
(* explicit inverse (Bezout reconstruction) *)
Theorem crt_iso : forall m n, 0 < m -> 0 < n -> rel_prime m n ->
  exists rec : Z -> Z -> Z,
       (forall a b, (rec a b) mod m = a mod m)                (* pi_m o rec = id *)
    /\ (forall a b, (rec a b) mod n = b mod n)                (* pi_n o rec = id *)
    /\ (forall x, (rec (x mod m) (x mod n)) mod (m * n) = x mod (m * n)). (* rec o pi = id *)
Proof.
  intros m n Hm Hn Hcop.
  destruct (rel_prime_bezout m n Hcop) as [u v Hbez].
  exists (recon u v m n); split; [ | split ].
  - intros a b; apply crt_proj_m with (u := u) (v := v); [ exact Hbez | lia ].
  - intros a b; apply crt_proj_n with (u := u) (v := v); [ exact Hbez | lia ].
  - intros x; apply crt_roundtrip; assumption.
Qed.

(* reduction mod k is a RING HOMOMORPHISM (Z -> Z/kZ): it respects     *)
(* addition and multiplication -- so the CRT bijection is a ring iso.  *)
Definition red_add := Zplus_mod.   (* (x+y) mod k = (x mod k + y mod k) mod k *)
Definition red_mul := Zmult_mod.   (* (x*y) mod k = (x mod k * (y mod k)) mod k *)

(* ----------------------------------------------------------------- *)
(*  (2) THE INVERSE SYSTEM  lim_n Z/nZ                               *)
(* ----------------------------------------------------------------- *)

(* the projections commute: reducing mod n then mod d (d | n) equals   *)
(* reducing mod d.  This is the compatibility that DEFINES the limit.  *)
Lemma proj_compat : forall d n x, 0 < d -> 0 < n -> (d | n) ->
  (x mod n) mod d = x mod d.
Proof. intros d n x Hd Hn Hdiv; symmetry; apply Zmod_div_mod; assumption. Qed.

(* the prime-power tower  Z/p^{k+1} -> Z/p^k  is an instance *)
Lemma tower_proj : forall p k x, 0 < p ->
  (x mod (p ^ Z.of_nat (S k))) mod (p ^ Z.of_nat k) = x mod (p ^ Z.of_nat k).
Proof.
  intros p k x Hp; apply proj_compat.
  - apply Z.pow_pos_nonneg; lia.
  - apply Z.pow_pos_nonneg; lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    exists p; ring.
Qed.

(* the index set is DIRECTED: any two levels divide their product,     *)
(* so the system is cofiltered (a genuine inverse system) *)
Lemma system_directed : forall m n, (m | m * n) /\ (n | m * n).
Proof. intros m n; split; [ apply Z.divide_factor_l | apply Z.divide_factor_r ]. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem profinite_crt :
  (* (1) CRT ring iso  Z/mnZ ~= Z/mZ x Z/nZ  for coprime m,n *)
  (forall m n, 0 < m -> 0 < n -> rel_prime m n ->
     exists rec : Z -> Z -> Z,
          (forall a b, (rec a b) mod m = a mod m)
       /\ (forall a b, (rec a b) mod n = b mod n)
       /\ (forall x, (rec (x mod m) (x mod n)) mod (m * n) = x mod (m * n)))
  (* (2) reduction is a ring homomorphism *)
  /\ (forall x y k, (x + y) mod k = ((x mod k) + (y mod k)) mod k)
  /\ (forall x y k, (x * y) mod k = ((x mod k) * (y mod k)) mod k)
  (* (3) the inverse system lim_n Z/nZ: projections commute ... *)
  /\ (forall d n x, 0 < d -> 0 < n -> (d | n) -> (x mod n) mod d = x mod d)
  (* ... and the index is directed *)
  /\ (forall m n, (m | m * n) /\ (n | m * n)).
Proof.
  split; [ exact crt_iso | ].
  split; [ exact Zplus_mod | ].
  split; [ exact Zmult_mod | ].
  split; [ exact proj_compat | exact system_directed ].
Qed.

Print Assumptions profinite_crt.

(* ================================================================= *)
(*  END ProfiniteCRT.v                                               *)
(*                                                                    *)
(*  Zhat = lim_n Z/nZ made explicit as a cofiltered inverse system of  *)
(*  finite rings with commuting reduction projections, together with   *)
(*  the CRT ring isomorphism Z/mnZ ~= Z/mZ x Z/nZ whose iterate over   *)
(*  n = prod_p p^{v_p} gives Zhat ~= prod_p Z_p (Z_p = lim_k Z/p^kZ,    *)
(*  the prime-power tower tower_proj).  This is the finite / non-       *)
(*  archimedean factor A_f of the adele ring A_Q = R x A_f             *)
(*  (ProductFormulaQ): built from finite discrete data, AXIOM-FREE.    *)
(*  The archimedean factor R = Q_infinity -- the metric completion, and *)
(*  hence Gamma-factors, xi(s), the functional equation, zeta special   *)
(*  values -- is the SEPARATE factor this construction never reaches;   *)
(*  it needs the quarantined Reals axioms.  Closed under the global     *)
(*  context.                                                          *)
(* ================================================================= *)
