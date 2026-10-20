(** Actual diagonal/point assignment bounds and ordinary membership-block
 consumers. Internally many parameter entries are kept exact. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceFiniteCutoffShift SourceWitnessThetaInstances SourceWitnessThetaMatrixActions SourceWitnessPointMembers SourceSubstitutionBounds
 NumericalSubstitutionMaps NumericalEnvironments NumericalContexts NumericalSourceFull SourceMembershipBlocks SourceMembershipBlockProofs.
Unset Implicit Arguments.
Theorem source_witness_diagonal_lookup_cases M p delta db dc n i name:
 source_witness_diagonal_map M p delta db dc->coding_lt M i(source_succ_iter M 4 n)->
 substitution_lookup M db dc(code_numeral M 4)delta i name->
 name=p \/exists j,coding_lt M j n /\name=addM M delta j.
Proof.
 intros HM HI HName. destruct(environment_lt_cases M i(code_numeral M 4))as[HIn|HOut].
 - destruct(source_numeral_initial_segment M 4 i HIn)as(j&HJ&->). left.
   exact(substitution_lookup_functional M _ _ _ _ _ name p HName(HM j HJ)).
 - apply substitution_lookup_outside in HName;[|exact HOut]. destruct HName as(j&EI&EN).
   right. exists j. split;[|exact EN].
   rewrite<-(witness_iter_add M 4 j)in EI. subst i. cbn[source_succ_iter]in HI.
   do 4 apply(proj1(coding_lt_succ_cancel M _ _))in HI. exact HI.
Qed.
Theorem source_witness_diagonal_maps_bound M p delta db dc n k:
 source_witness_diagonal_map M p delta db dc->coding_lt M p k->
 (forall j,coding_lt M j n->coding_lt M(addM M j delta)k)->
 substitution_maps_bound M db dc(code_numeral M 4)delta(source_succ_iter M 4 n)k.
Proof.
 intros HM HP HNames i name HI HName.
 destruct(source_witness_diagonal_lookup_cases M p delta db dc n i name HM HI HName)as[E|(j&HJ&E)];subst name;[exact HP|].
 rewrite Arithmetic.add_comm. exact(HNames j HJ).
Qed.
Theorem source_witness_point_maps_bound M p s t delta db dc pb pc count k:
 source_witness_diagonal_map M p delta db dc->source_witness_point_map M p s t delta pb pc->
 coding_lt M p k->coding_lt M s k->coding_lt M t k->
 substitution_maps_bound M db dc(code_numeral M 4)delta count k->
 substitution_maps_bound M pb pc(code_numeral M 4)(succM M delta)count(succM M k).
Proof.
 intros HD HP BP BS BT HMap i name HI HName.
 destruct(source_witness_point_lookup_cases M p s t delta db dc pb pc i name HD HP HName)
  as[E|[E|[E|[E|(old&HOld&E)]]]];subst name.
 - apply coding_zero_lt_succ.
 - exact(proj2(coding_lt_succ_cancel M p k)BP).
 - exact(proj2(coding_lt_succ_cancel M s k)BS).
 - exact(proj2(coding_lt_succ_cancel M t k)BT).
 - exact(proj2(coding_lt_succ_cancel M old k)(HMap i old HI HOld)).
Qed.
Theorem source_full_witness_diagonal_members M p delta db dc n carrier block pY gb gc gn k:
 source_witness_diagonal_map M p delta db dc->context_bounded M gb gc gn k->coding_lt M carrier k->
 (forall j,coding_lt M j n->coding_lt M(addM M j delta)k)->
 source_membership_block M delta carrier n block->sf_relation M SFMember p carrier pY->
 source_full_prv M gb gc gn block->source_full_prv M gb gc gn pY->
 forall i name member,coding_lt M i(source_succ_iter M 4 n)->
 substitution_lookup M db dc(code_numeral M 4)delta i name->
 sf_relation M SFMember name carrier member->source_full_prv M gb gc gn member.
Proof.
 intros HM BC HY HNames HBlock HPY PBlock PPY i name member HI HName HMember.
 destruct(source_witness_diagonal_lookup_cases M p delta db dc n i name HM HI HName)as[E|(j&HJ&E)];subst name.
 - pose proof(sf_relation_functional M SFMember p carrier pY member HPY HMember)as E. now subst member.
 - rewrite Arithmetic.add_comm in HMember.
   exact(source_full_membership_block_project M delta carrier n block gb gc gn k j member HNames HY HBlock BC PBlock HJ HMember).
Qed.
Print Assumptions source_witness_diagonal_lookup_cases.
Print Assumptions source_witness_diagonal_maps_bound.
Print Assumptions source_witness_point_maps_bound.
Print Assumptions source_full_witness_diagonal_members.
