(** The exact decreasing-rank arithmetic used by the published pair constructor. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section PairRank.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring pair_rank_ring:(model_semiring M).
Theorem program230_pair_rank_step a b k value rest:
 a+b = S k->pair_graph M a b value->pair_graph M Z k rest->value = b+S rest.
Proof.
 intros Hsum Hvalue Hrest. apply(double_cancel M).
 unfold pair_graph in Hvalue,Hrest. rewrite Hsum in Hvalue.
 rewrite coding_add_zero in Hrest.
 rewrite(succ_as_add M rest).
 replace(twoM M*(b+(rest+S Z)))with(twoM M*rest+twoM M*b+twoM M)by ring.
 rewrite Hrest,Hvalue. unfold twoM.
 rewrite(succ_as_add M(S k)),(succ_as_add M k),(succ_as_add M(S Z)).
 ring.
Qed.
Theorem program230_pair_rank_zero a b value:
 a+b = Z->pair_graph M a b value->a = Z /\b = Z /\value = Z.
Proof.
 intros Hsum Hpair.
 destruct(@Peano.sum_is_zero(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)a b Hsum)as[Ha Hb].
 subst a b. split;[reflexivity|]. split;[reflexivity|].
 exact(pair_functional M Z Z value Z Hpair(pair_zero M)).
Qed.
End PairRank.
Print Assumptions program230_pair_rank_step.
Print Assumptions program230_pair_rank_zero.
