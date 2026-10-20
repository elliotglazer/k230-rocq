(** Arithmetic facts for the actual unpair-body successor. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Lemma program230_pair_walk_total M x y:exists x' y',pair_walk M x y x' y'.
Proof.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)x)as[H0|[u Hu]].
 -exists(succM M y),(zeroM M);left;auto.
 -exists u,(succM M y);right;exists u;auto.
Qed.
Lemma program230_pair_walk_successor M x y x' y' index:
 pair_graph M x y index->pair_walk M x y x' y'->pair_graph M x' y'(succM M index).
Proof.
 intros HP[[Hx[Hx' Hy']]|[u[Hx[Hx' Hy']]]].
 -subst x x' y';exact(pair_successor_diagonal M y index HP).
 -subst x x' y';exact(pair_successor_left M u y index HP).
Qed.
Print Assumptions program230_pair_walk_total.
Print Assumptions program230_pair_walk_successor.
