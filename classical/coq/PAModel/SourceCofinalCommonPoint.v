(** Literal open cofinal-common-level matrices, with arbitrary model-valued
    parameter count. The chosen ordinal is explicitly a member of K. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceQuantifierRules SourceDomainInstances SourceUnarySubstitution
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceHierarchySyntax
  SourceOrdinalPredicate SourceMembershipBlocks SourceMembershipBlockProofs SourceMembershipBlockSubstitution
  SourceCommonLevelPoint SourceCommonLevelRecipe.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque source_ordinal_predicate_code.

Definition source_cofinal_common_point M start count K d y out :=exists common member,
 source_common_level_point M start count d y common /\
 sf_relation M SFMember d K member /\sf_relation M SFAnd member common out.

Theorem source_cofinal_common_point_total M start count K d y :exists out,
 source_cofinal_common_point M start count K d y out.
Proof.
 destruct(source_common_level_point_total M start count d y)as(common&HC).
 destruct(sf_relation_total M SFMember d K)as(member&HM).
 destruct(sf_relation_total M SFAnd member common)as(out&HO).
 exists out,common,member. auto.
Qed.
Lemma source_common_level_point_functional M start count d y f g :
 source_common_level_point M start count d y f ->source_common_level_point M start count d y g ->f=g.
Proof.
 intros(m&o&l&p&HM&HO&HL&HP&HF)(m'&o'&l'&p'&HM'&HO'&HL'&HP'&HG).
 pose proof(source_membership_block_functional M start y count m m' HM HM')as E. subst m'.
 pose proof(numerical_instantiation_functional M _ d o o' HO HO')as E. subst o'.
 pose proof(source_LL_instance_functional M d y l l' HL HL')as E. subst l'.
 pose proof(sf_relation_functional M SFAnd o l p p' HP HP')as E. subst p'.
 exact(sf_relation_functional M SFAnd p m f g HF HG).
Qed.
Theorem source_cofinal_common_point_functional M start count K d y f g :
 source_cofinal_common_point M start count K d y f ->
 source_cofinal_common_point M start count K d y g ->f=g.
Proof.
 intros(c&m&HC&HM&HF)(c'&m'&HC'&HM'&HG).
 pose proof(source_common_level_point_functional M start count d y c c' HC HC')as E. subst c'.
 pose proof(sf_relation_functional M SFMember d K m m' HM HM')as E. subst m'.
 exact(sf_relation_functional M SFAnd m c f g HF HG).
Qed.
Theorem source_cofinal_common_point_bounded M start count K d y out k :
 (forall i,coding_lt M i count ->coding_lt M(addM M i start)k) ->
 coding_lt M K k ->coding_lt M d k ->coding_lt M y k ->
 source_cofinal_common_point M start count K d y out ->source_bounded M out k.
Proof.
 intros HN HK HD HY(common&member&HC&HM&HO).
 apply(proj2(source_bounded_accept_binary M SFAnd member common out k(or_introl eq_refl)HO)). split.
 - exact(proj2(source_bounded_accept_atom M SFMember d K member k(or_introl eq_refl)HM)(conj HD HK)).
 - exact(source_common_level_point_bounded M start count d y common k HN HD HY HC).
Qed.
Theorem source_cofinal_common_point_substitution M start count K d y out start' K' d' y' out' b c l base :
 source_cofinal_common_point M start count K d y out ->
 source_cofinal_common_point M start' count K' d' y' out' ->
 substitution_lookup M b c l base K K' ->substitution_lookup M b c l base d d' ->
 substitution_lookup M b c l base y y' ->
 (forall i,coding_lt M i count ->substitution_lookup M b c l base(addM M i start)(addM M i start')) ->
 numerical_substitution M out b c l base out'.
Proof.
 intros(common&member&HC&HM&HO)(common'&member'&HC'&HM'&HO')HK HD HY HN.
 apply(proj2(numerical_substitution_binary M SFAnd member common out b c l base out'(or_introl eq_refl)HO)).
 exists member',common'. split.
 - apply(proj2(numerical_substitution_member M d K member b c l base member' HM)).
   exists d',K'. auto.
 - split;[exact(source_common_level_point_substitution M start count d y common start' d' y' common' b c l base HC HC' HD HY HN)|exact HO'].
Qed.

Definition source_cofinal_common_point_data M ordcode start count K d y out :=exists members ordinal level pair common member,
 source_membership_block M start y count members /\numerical_instantiation M ordcode d ordinal /\
 source_LL_instance M d y level /\sf_relation M SFAnd ordinal level pair /\
 sf_relation M SFAnd pair members common /\sf_relation M SFMember d K member /\sf_relation M SFAnd member common out.
Definition source_cofinal_common_point_formula(ordcode start count K d y out:term):form :=
 ∃∃∃∃∃∃ (source_membership_block_formula(source_common_lift6 start)(source_common_lift6 y)(source_common_lift6 count)$5 ∧
 numerical_instantiation_formula(source_common_lift6 ordcode)(source_common_lift6 d)$4 ∧
 source_LL_literal_formula(source_common_lift6 d)(source_common_lift6 y)$3 ∧
 sf_formula SFAnd $4 $3 $2 ∧sf_formula SFAnd $2 $5 $1 ∧
 sf_formula SFMember(source_common_lift6 d)(source_common_lift6 K)$0 ∧sf_formula SFAnd $0 $1(source_common_lift6 out)).
Local Opaque holds source_membership_block_formula numerical_instantiation_formula source_LL_literal_formula sf_formula.
Theorem source_cofinal_common_point_formula_correct M rho ordcode start count K d y out :
 holds M rho(source_cofinal_common_point_formula ordcode start count K d y out) <->
 source_cofinal_common_point_data M(evalM M rho ordcode)(evalM M rho start)(evalM M rho count)
 (evalM M rho K)(evalM M rho d)(evalM M rho y)(evalM M rho out).
Proof.
 unfold source_cofinal_common_point_formula,source_cofinal_common_point_data.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite source_membership_block_formula_correct.
 setoid_rewrite numerical_instantiation_formula_correct.
 setoid_rewrite source_LL_literal_formula_correct.
 setoid_rewrite sf_formula_correct. setoid_rewrite source_common_eval_lift6.
 split;intros(m&o&l&p&c&h&H);exists m,o,l,p,c,h;tauto.
Qed.
Lemma source_cofinal_common_point_data_actual M start count K d y out :
 source_cofinal_common_point_data M(source_ordinal_predicate_code M)start count K d y out <->
 source_cofinal_common_point M start count K d y out.
Proof.
 unfold source_cofinal_common_point_data,source_cofinal_common_point,source_common_level_point.
 split.
 - intros(m&o&l&p&c&h&HM&HO&HL&HP&HC&HH&HF). exists c,h. split;[exists m,o,l,p;auto|auto].
 - intros(c&h&(m&o&l&p&HM&HO&HL&HP&HC)&HH&HF). exists m,o,l,p,c,h. repeat first[assumption|split].
Qed.
Print Assumptions source_cofinal_common_point_total.
Print Assumptions source_cofinal_common_point_substitution.
Print Assumptions source_cofinal_common_point_formula_correct.
