(** Literal numerical substitution through an internally finite membership block. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceContextConjunctionSubstitution SourceMembershipBlocks.
Unset Implicit Arguments.

Theorem source_membership_block_substitution M start y n f start' y' g b c l base :
  source_membership_block M start y n f ->source_membership_block M start' y' n g ->
  substitution_lookup M b c l base y y' ->
  (forall i,coding_lt M i n ->substitution_lookup M b c l base (addM M i start)(addM M i start')) ->
  numerical_substitution M f b c l base g.
Proof.
  intros [sb [sc [HS HF]]] [tb [tc [HT HG]]] HY HNames.
  apply (source_context_conjunction_substitution M sb sc tb tc b c l base n f g HF HG).
  intros i a d HI HA HD.
  apply (proj2 (numerical_substitution_member M (addM M i start) y a b c l base d (HS i a HI HA))).
  exists (addM M i start'),y'. split;[exact(HNames i HI)|]. split;[exact HY|exact(HT i d HI HD)].
Qed.
Theorem source_membership_block_instantiation M start y n f start' y' g t :
  source_membership_block M start y n f ->source_membership_block M start' y' n g ->
  (forall b c,substitution_lookup M b c (succM M(zeroM M))(zeroM M)(zeroM M) t ->
    substitution_lookup M b c (succM M(zeroM M))(zeroM M) y y') ->
  (forall b c,substitution_lookup M b c (succM M(zeroM M))(zeroM M)(zeroM M) t ->
    forall i,coding_lt M i n ->
      substitution_lookup M b c (succM M(zeroM M))(zeroM M) (addM M i start)(addM M i start')) ->
  numerical_instantiation M f t g.
Proof.
  intros HF HG HY HNames.
  destruct(substitution_singleton_total M t) as(b&c&HH&HT).
  exists b,c. split;[exact HH|].
  exact(source_membership_block_substitution M start y n f start' y' g b c
    (succM M(zeroM M))(zeroM M) HF HG (HY b c HH)(HNames b c HH)).
Qed.
Print Assumptions source_membership_block_substitution.
Print Assumptions source_membership_block_instantiation.
