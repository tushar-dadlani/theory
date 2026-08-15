(* ================================================================= *)
(*  Ell2Symmetry.v   (the Zhat^x character symmetry of the BC triple)    *)
(*                                                                    *)
(*  The Bost-Connes symmetry group is the profinite unit group           *)
(*  Zhat^x = prod_p Z_p^x; its Pontryagin dual is the group of            *)
(*  Dirichlet characters, i.e. the completely-multiplicative unimodular   *)
(*  symbols  chi : N -> R  (a character of (Z/m)^x at each finite level).  *)
(*  Each such chi acts on the spectral triple (Ell2, D = diag(log n)) as   *)
(*  a diagonal symmetry  U_chi = Dmul chi, and:                          *)
(*                                                                    *)
(*    * U_chi commutes with D            (symmetry of the dynamics),      *)
(*    * U_chi (crea p .) = chi(p) . crea p (U_chi .)   (equivariance,     *)
(*        the character phase chi(p) on mode p),                         *)
(*    * the symbols compose as a group:  U_c U_d = U_{c.d},  U_1 = I,     *)
(*    * the twisted partition function is the L-series                    *)
(*        Tr(U_chi e^{-b D}) = sum chi(n) n^{-b}   ( = zeta for chi=1,     *)
(*        an L(b,chi) for a Dirichlet character), converging for b>1.     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (+ functional_extensionality). *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List FunctionalExtensionality.
Require Import Ell2 Ell2Operator Ell2Basis Ell2Zeta Ell2Fock Ell2SpectralTriple
        Ell2ZetaConverge Ell2Partition HagedornTransition CSeries.
Open Scope R_scope.

(* --- the group structure of the symmetries (independent of any axioms) --- *)

(* composing symmetries = multiplying the characters *)
Lemma sym_compose : forall (c d : nat -> R) f n,
  Dmul (fun k => c k * d k) f n = Dmul c (Dmul d f) n.
Proof. intros; unfold Dmul; ring. Qed.

(* the trivial character is the identity symmetry *)
Lemma sym_trivial : forall f, Dmul (fun _ => 1) f = f.
Proof. intro f; apply functional_extensionality; intro n; unfold Dmul; ring. Qed.

Lemma diag_trace_succ : forall a N, diag_trace a (S N) = (diag_trace a N + a (S N))%R.
Proof.
  intros a N. rewrite !diag_trace_eq.
  rewrite seq_S, map_app, fold_Rplus_app; simpl.
  replace (1 + N)%nat with (S N) by lia. ring.
Qed.

(* ------------------------------------------------------------------ *)
Section Character.
Variable chi : nat -> R.
Hypothesis chi_1 : chi 1 = 1.
Hypothesis chi_mult : forall m n, chi (m * n)%nat = (chi m * chi n)%R.
Hypothesis chi_unimod : forall n, Rabs (chi n) <= 1.

(* the symmetry operator  U_chi = Dmul chi *)
Definition sym (f : nat -> R) : nat -> R := Dmul chi f.

(* U_chi commutes with D : symmetry of the dynamics (of the Hamiltonian) *)
Lemma sym_commute_D : forall f n, Dop (sym f) n = sym (Dop f) n.
Proof. intros f n; unfold sym; apply Dop_diag_commute. Qed.

(* U_chi is equivariant on creations, with phase chi(p) on mode p *)
Theorem sym_crea_equivariant : forall p m n, (1 <= p)%nat ->
  sym (crea p (e m)) n = (chi p * crea p (sym (e m)) n)%R.
Proof.
  intros p m n Hp. unfold sym.
  assert (Hsm : Dmul chi (e m) = (fun k => chi m * e m k))
    by (apply functional_extensionality; intro k; apply Dmul_e).
  rewrite (crea_e p m Hp), Dmul_e, Hsm, crea_scal, (crea_e p m Hp), chi_mult. ring.
Qed.

(* the twisted partition function  Tr(U_chi e^{-b D}) = sum chi(n) n^{-b}  *)
(* converges for b > 1  (absolute convergence vs zeta).                    *)
Lemma trace_twist_shift : forall b N,
  diag_trace (fun n => chi n * z b n) (S N)
  = sum_f_R0 (fun k => chi (S k) * z b (S k)) N.
Proof.
  intros b N. induction N as [| N IH].
  - cbn [sum_f_R0]. rewrite diag_trace_succ.
    replace (diag_trace (fun n => chi n * z b n) 0) with 0 by reflexivity.
    rewrite Rplus_0_l. reflexivity.
  - rewrite diag_trace_succ, IH, tech5. reflexivity.
Qed.

Theorem twisted_partition_is_L : forall b, 1 < b ->
  { L : R | Un_cv (fun N => diag_trace (fun n => chi n * z b n) N) L }.
Proof.
  intros b Hb.
  assert (Hbound : forall k,
     Rabs (chi (S k) * z b (S k)) <= Rpower (INR (S k)) (- b)).
  { intro k. rewrite Rabs_mult.
    assert (Hz : z b (S k) = Rpower (INR (S k)) (- b)) by (unfold z; reflexivity).
    rewrite Hz, (Rabs_right (Rpower (INR (S k)) (- b)));
      [ | apply Rle_ge; left; unfold Rpower; apply exp_pos ].
    rewrite <- (Rmult_1_l (Rpower (INR (S k)) (- b))) at 2.
    apply Rmult_le_compat_r; [ left; unfold Rpower; apply exp_pos | apply chi_unimod ]. }
  destruct (Rseries_abs_cv (fun k => chi (S k) * z b (S k))
              (fun k => Rpower (INR (S k)) (- b)) Hbound (Zpart_cv b Hb)) as [L HS].
  exists L. apply Un_cv_unshift.
  apply (Un_cv_ext' (sum_f_R0 (fun k => chi (S k) * z b (S k))));
    [ intro N; symmetry; apply trace_twist_shift | exact HS ].
Qed.

(* the untwisted (trivial-character) case recovers zeta *)
Corollary twisted_partition_zeta_when_trivial :
  (forall n, chi n = 1) -> forall b, 1 < b ->
  { L : R | Un_cv (fun N => diag_trace (z b) N) L }.
Proof.
  intros Htriv b Hb. destruct (twisted_partition_is_L b Hb) as [L HS].
  exists L. apply (Un_cv_ext' (fun N => diag_trace (fun n => chi n * z b n) N));
    [ | exact HS ].
  intro N. rewrite !diag_trace_eq. f_equal. apply map_ext.
  intro n. rewrite Htriv. ring.
Qed.

(* the full character symmetry, bundled *)
Theorem character_symmetry : forall b, 1 < b ->
  (* symmetry of the dynamics : U_chi commutes with D *)
  (forall f n, Dop (sym f) n = sym (Dop f) n)
  (* equivariance on the modes with phase chi(p) *)
  * (forall p m n, (1 <= p)%nat -> sym (crea p (e m)) n = chi p * crea p (sym (e m)) n)
  (* the twisted partition function Tr(U_chi e^{-bD}) = L(b,chi) converges *)
  * { L : R | Un_cv (fun N => diag_trace (fun n => chi n * z b n) N) L }.
Proof.
  intros b Hb. repeat split.
  - apply sym_commute_D.
  - apply sym_crea_equivariant.
  - apply twisted_partition_is_L; exact Hb.
Qed.

End Character.

Print Assumptions character_symmetry.
