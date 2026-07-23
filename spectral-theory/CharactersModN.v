(* ================================================================= *)
(*  CharactersModN.v                                                 *)
(*                                                                    *)
(*  THE CHARACTER GROUP OF Z/NZ, from the roots of unity -- the       *)
(*  finite-abelian-group orthogonality underlying Dirichlet chars.    *)
(*                                                                    *)
(*  The characters of the cyclic group (Z/NZ, +) are                  *)
(*     chi_a (n)  =  (w N)^(a n)  =  exp(2 pi i a n / N),   a in Z/NZ, *)
(*  and they form a group isomorphic to Z/NZ (the dual group).  We    *)
(*  prove:                                                            *)
(*    chi_add    : chi_a(m+n) = chi_a(m) chi_a(n)   (a character)      *)
(*    chi_0      : chi_a(0) = 1                                        *)
(*    chi_pow_N  : chi_a(n)^N = 1   (values are N-th roots of unity)   *)
(*    chi_mul    : chi_a . chi_b = chi_{a+b}   (dual group Z/NZ)       *)
(*    chi_periodic_n : chi_a(n+N) = chi_a(n)   (well-defined on Z/NZ)  *)
(*  and the TWO ORTHOGONALITY RELATIONS:                              *)
(*    char_orthogonality_row : sum_{n<N} chi_a(n) conj(chi_b(n))       *)
(*                               = N if a=b else 0                    *)
(*    char_orthogonality_col : sum_{a<N} chi_a(n) conj(chi_a(m))       *)
(*                               = N if n=m else 0                    *)
(*  These are exactly the DFT orthogonality (orthogonality_2) read in  *)
(*  character-theory language: the rows/columns of the character       *)
(*  table are orthogonal, with squared norm N.                        *)
(*                                                                    *)
(*  HONEST SCOPE.  These are the characters of the CYCLIC group Z/NZ.  *)
(*  A Dirichlet character mod N is a character of the MULTIPLICATIVE   *)
(*  group (Z/NZ)^* ; when (Z/NZ)^* is cyclic (e.g. N prime) it is      *)
(*  isomorphic to a cyclic group and its characters are exactly these  *)
(*  (via a primitive root / discrete log) -- so this is the abelian    *)
(*  orthogonality at the heart of Dirichlet character theory.  Full    *)
(*  Dirichlet theory (the group (Z/NZ)^*, primitivity, L-series /      *)
(*  Euler products) needs the multiplicative structure, NOT built here. *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via C / trig).      *)
(* ================================================================= *)

From Stdlib Require Import Reals Arith Lia.
Require Import ComplexField RootsOfUnity DFTInversion.
Open Scope R_scope.

(* the character chi_a of Z/NZ, evaluated at n *)
Definition chi (N a n : nat) : C := Cpow (w N) (a * n).

(* conjugation turns a w-power into a wc-power *)
Lemma conj_w_pow : forall N j, Cconj (Cpow (w N) j) = Cpow (wc N) j.
Proof. intros N j; unfold wc; symmetry; apply Cconj_pow. Qed.

(* ----------------------------------------------------------------- *)
(*  chi is a character of (Z/NZ, +), valued in the N-th roots of unity *)
(* ----------------------------------------------------------------- *)

Lemma chi_add : forall N a m n, chi N a (m + n) = Cmul (chi N a m) (chi N a n).
Proof.
  intros N a m n; unfold chi.
  replace (a * (m + n))%nat with (a * m + a * n)%nat by lia; apply Cpow_add.
Qed.

Lemma chi_0 : forall N a, chi N a 0 = C1.
Proof. intros N a; unfold chi; rewrite Nat.mul_0_r; reflexivity. Qed.

Lemma chi_pow_N : forall N a n, (0 < N)%nat -> Cpow (chi N a n) N = C1.
Proof.
  intros N a n HN; unfold chi.
  rewrite <- Cpow_mul, (Nat.mul_comm (a * n) N), Cpow_mul, (w_pow_N N HN), Cpow_C1.
  reflexivity.
Qed.

(* the dual group law: characters multiply by adding their labels *)
Lemma chi_mul : forall N a b n, Cmul (chi N a n) (chi N b n) = chi N (a + b) n.
Proof.
  intros N a b n; unfold chi; rewrite <- Cpow_add; f_equal; lia.
Qed.

(* well-defined on Z/NZ: periodic in n with period N *)
Lemma chi_periodic_n : forall N a n, (0 < N)%nat -> chi N a (n + N) = chi N a n.
Proof.
  intros N a n HN; unfold chi.
  replace (a * (n + N))%nat with (a * n + N * a)%nat by lia.
  rewrite Cpow_add, (Cpow_mul (w N) N a), (w_pow_N N HN), Cpow_C1; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE ORTHOGONALITY RELATIONS  (character-table rows/columns)       *)
(* ----------------------------------------------------------------- *)

(* first (row) orthogonality: distinct characters are orthogonal *)
Theorem char_orthogonality_row : forall N a b,
  (0 < N)%nat -> (a < N)%nat -> (b < N)%nat ->
  Csum (fun n => Cmul (chi N a n) (Cconj (chi N b n))) N
  = if Nat.eqb a b then RtoC (INR N) else C0.
Proof.
  intros N a b HN Ha Hb.
  rewrite (Csum_ext
    (fun n => Cmul (chi N a n) (Cconj (chi N b n)))
    (fun n => Cmul (Cpow (wc N) (n * b)) (Cpow (w N) (n * a))) N).
  2:{ intro n; unfold chi; rewrite conj_w_pow, (Nat.mul_comm a n), (Nat.mul_comm b n); ring. }
  exact (orthogonality_2 N a b Ha Hb).
Qed.

(* second (column) orthogonality: the columns of the character table *)
Theorem char_orthogonality_col : forall N n m,
  (0 < N)%nat -> (n < N)%nat -> (m < N)%nat ->
  Csum (fun a => Cmul (chi N a n) (Cconj (chi N a m))) N
  = if Nat.eqb n m then RtoC (INR N) else C0.
Proof.
  intros N n m HN Hn Hm.
  rewrite (Csum_ext
    (fun a => Cmul (chi N a n) (Cconj (chi N a m)))
    (fun a => Cmul (Cpow (wc N) (a * m)) (Cpow (w N) (a * n))) N).
  2:{ intro a; unfold chi; rewrite conj_w_pow; ring. }
  exact (orthogonality_2 N n m Hn Hm).
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem characters_of_Z_mod_N : forall N, (0 < N)%nat ->
  (* chi_a is a character of (Z/NZ, +) valued in the N-th roots of unity *)
     (forall a m n, chi N a (m + n) = Cmul (chi N a m) (chi N a n))
  /\ (forall a, chi N a 0 = C1)
  /\ (forall a n, Cpow (chi N a n) N = C1)
  (* the dual group is Z/NZ: chi_a . chi_b = chi_{a+b} *)
  /\ (forall a b n, Cmul (chi N a n) (chi N b n) = chi N (a + b) n)
  (* orthogonality of rows and of columns of the character table *)
  /\ (forall a b, (a < N)%nat -> (b < N)%nat ->
        Csum (fun n => Cmul (chi N a n) (Cconj (chi N b n))) N
        = if Nat.eqb a b then RtoC (INR N) else C0)
  /\ (forall n m, (n < N)%nat -> (m < N)%nat ->
        Csum (fun a => Cmul (chi N a n) (Cconj (chi N a m))) N
        = if Nat.eqb n m then RtoC (INR N) else C0).
Proof.
  intros N HN.
  repeat split; intros.
  - apply chi_add.
  - apply chi_0.
  - apply chi_pow_N; exact HN.
  - apply chi_mul.
  - apply char_orthogonality_row; assumption.
  - apply char_orthogonality_col; assumption.
Qed.

Print Assumptions characters_of_Z_mod_N.

(* ================================================================= *)
(*  END CharactersModN.v                                             *)
(*  The characters chi_a(n) = (w N)^(a n) of the cyclic group Z/NZ,    *)
(*  their dual group Z/NZ, and the two orthogonality relations of the  *)
(*  character table (= the DFT orthogonality in character language).   *)
(*  This is the finite-abelian-group orthogonality underlying          *)
(*  Dirichlet characters; the multiplicative group (Z/NZ)^* and full   *)
(*  Dirichlet L-theory are NOT built here.  Uses the classical Reals   *)
(*  axioms (quarantined).                                             *)
(* ================================================================= *)
