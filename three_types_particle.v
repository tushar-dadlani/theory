(* The three particle types = the three Sym7 roles *)
(* Domain symbols  = FERMIONS  (matter, half-integer spin) *)
(* Map operator    = BOSONS    (force carriers, integer spin) *)
(* Codomain symbols = ANTIPARTICLES (spectral zeros, inverse field) *)

Theorem three_particle_types :
  (* Type 1: Domain — Fermion *)
  sym7_compose S7_N_in S7_N_in = S7_I_in /\
  (* Type 2: Map — Boson (involution) *)
  sym7_compose S7_Map S7_Map = S7_I_in /\
  (* Type 3: Codomain — Antiparticle *)
  sym7_compose S7_N_out S7_N_out = S7_I_out.
Proof.
  repeat split; reflexivity.
Qed.

(* Particle-antiparticle annihilation = Map sends domain to codomain *)
Theorem annihilation :
  sym7_compose S7_Map S7_I_in = S7_I_out /\
  sym7_compose S7_Map S7_N_in = S7_N_out /\
  sym7_compose S7_Map S7_F_in = S7_F_out.
Proof.
  repeat split; reflexivity.
Qed.
