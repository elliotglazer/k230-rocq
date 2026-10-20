(** Actual literal common-level matrices, with arbitrary internally coded
    parameter count and chosen ordinal/carrier names. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceQuantifierRules SourceDomainInstances SourceUnarySubstitution
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceHierarchySyntax
  SourceOrdinalPredicate SourceMembershipBlocks SourceMembershipBlockProofs SourceMembershipBlockSubstitution.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_common_level_point M start count ordinalname carriername out :=
  exists members ordinal level pair,
    source_membership_block M start carriername count members /\
    numerical_instantiation M (source_ordinal_predicate_code M) ordinalname ordinal /\
    source_LL_instance M ordinalname carriername level /\
    sf_relation M SFAnd ordinal level pair /\sf_relation M SFAnd pair members out.

Theorem source_common_level_point_total M start count d y :exists out,
  source_common_level_point M start count d y out.
Proof.
  destruct(source_membership_block_total M start y count) as(members&HM).
  destruct(numerical_instantiation_total M (source_ordinal_predicate_code M)d) as(ordinal&HO).
  destruct(source_LL_instance_total M d y) as(level&HL).
  destruct(sf_relation_total M SFAnd ordinal level) as(pair&HP).
  destruct(sf_relation_total M SFAnd pair members) as(out&HF).
  exists out,members,ordinal,level,pair. repeat first[assumption|split].
Qed.
Theorem source_common_level_point_bounded M start count d y out k :
  (forall i,coding_lt M i count ->coding_lt M (addM M i start) k) ->
  coding_lt M d k ->coding_lt M y k ->source_common_level_point M start count d y out ->
  source_bounded M out k.
Proof.
  intros HNames HD HY (members&ordinal&level&pair&HM&HO&HL&HP&HF).
  apply(proj2(source_bounded_accept_binary M SFAnd pair members out k(or_introl eq_refl)HF)). split.
  - apply(proj2(source_bounded_accept_binary M SFAnd ordinal level pair k(or_introl eq_refl)HP)). split.
    + exact(source_domain_instance_bound M _ d ordinal k(source_ordinal_predicate_bounded M)HD HO).
    + exact(source_LL_instance_bounded M d y level k HD HY HL).
  - exact(source_membership_block_bound M start y count members k HNames HY HM).
Qed.
Theorem source_common_level_point_substitution M start count d y out start' d' y' out' b c l base :
  source_common_level_point M start count d y out ->
  source_common_level_point M start' count d' y' out' ->
  substitution_lookup M b c l base d d' ->substitution_lookup M b c l base y y' ->
  (forall i,coding_lt M i count ->substitution_lookup M b c l base(addM M i start)(addM M i start')) ->
  numerical_substitution M out b c l base out'.
Proof.
  intros (members&ordinal&level&pair&HM&HO&HL&HP&HF)
    (members'&ordinal'&level'&pair'&HM'&HO'&HL'&HP'&HF') HD HY HNames.
  apply(proj2(numerical_substitution_binary M SFAnd pair members out b c l base out'(or_introl eq_refl)HF)).
  exists pair',members'. split.
  - apply(proj2(numerical_substitution_binary M SFAnd ordinal level pair b c l base pair'(or_introl eq_refl)HP)).
    exists ordinal',level'. split.
    + exact(source_domain_instance_substitution_graph M _ d ordinal b c l base d' ordinal'
        (source_ordinal_predicate_bounded M)HO HD HO').
    + split;[exact(source_LL_instance_substitution M d y level d' y' level' b c l base HL HL' HD HY)|exact HP'].
  - split;[exact(source_membership_block_substitution M start y count members start' y' members' b c l base HM HM' HY HNames)|exact HF'].
Qed.
Print Assumptions source_common_level_point_total.
Print Assumptions source_common_level_point_bounded.
Print Assumptions source_common_level_point_substitution.
