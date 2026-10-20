(** The actual hierarchy-existence law discharges PH's subcarrier
    existential. Only the ordinary ordinal/subset hypotheses remain. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalInstantiation NumericalRenamingMaps NumericalRenaming
 SourceHierarchySyntax SourceEwMonotone SourceEwAtSyntax SourceRawSubset SourceRawSubsetBounds
 SourceMembershipBlocks SourceMembershipBlockProofs SourceOrdinalPredicate SourceDomainInstances
 SourcePieceConjunctionBounds SourceReflectionKFWitness SourceReflectionHierarchyWitness
 SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability SourcePHHierarchyElimination.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Lemma source_PH_raw_subset_functional M x y a b:source_raw_subset_graph M x y a ->source_raw_subset_graph M x y b ->a=b.
Proof.
 intros(l&r&p&HL&HR&HP&HA)(l'&r'&p'&HL'&HR'&HP'&HB).
 assert(E:l'=l)by(eapply sf_relation_functional;eassumption). subst l'.
 assert(E:r'=r)by(eapply sf_relation_functional;eassumption). subst r'.
 assert(E:p'=p)by(eapply sf_relation_functional;eassumption). subst p'.
 eapply sf_relation_functional;eassumption.
Qed.
Theorem source_zfr_PH_hierarchy_ordinals M domain level sb sc count K k w witness X lk beta Lb start
 entry params phi rb rc rn phi' block ow ob subset lb goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF_witness M domain level sb sc count K k w witness ->source_LL_instance M k X lk ->
 source_membership_block M start X params block ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 numerical_instantiation M(source_ordinal_predicate_code M)w ow ->numerical_instantiation M(source_ordinal_predicate_code M)beta ob ->
 source_raw_subset_graph M w beta subset ->source_LL_instance M beta Lb lb ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M w bound ->coding_lt M X bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[witness;lk;block;ow;ob;subset;lb]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HW HK HBlock HRL HR HOW HOB HSub HLb HEGoal BMatrix BK Bk BW BX Bbeta BLb HNames HLaw.
 destruct(source_zfr_reflection_hierarchy_witness_shell M w beta Lb)as(ow'&ob'&sub'&lb'&lw&included&body&ex&hyLaw&HOW'&HOB'&HSub'&HLb'&HY&HIncluded&HBody&HEx&HTel&PHy).
 assert(E:ow'=ow)by(eapply numerical_instantiation_functional;eassumption). subst ow'.
 assert(E:ob'=ob)by(eapply numerical_instantiation_functional;eassumption). subst ob'.
 assert(E:sub'=subset)by(eapply source_PH_raw_subset_functional;eassumption). subst sub'.
 assert(E:lb'=lb)by(eapply source_LL_instance_functional;eassumption). subst lb'.
 destruct(source_finite_telescope_total M[witness;lk;block;ex]goal)as(pointLaw&HPointLaw).
 pose proof(source_zfr_PH_hierarchy_elimination M domain level sb sc count K k w witness X lk Lb start
  entry params phi rb rc rn phi' block lw included body ex goal pointLaw bound
  HD HL HLg HV HE HP HW HK HBlock HRL HR HY HIncluded HBody HEx HEGoal BMatrix BK Bk BW BX BLb HNames HPointLaw)as PPoint.
 pose proof(source_reflection_KF_witness_bounded M domain level sb sc count K k w witness bound HD HL HV BK Bk BW HW)as BWit.
 pose proof(source_LL_instance_bounded M k X lk bound Bk BX HK)as BLK.
 pose proof(source_membership_block_bound M start X params block bound HNames BX HBlock)as BB.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)w ow bound(source_ordinal_predicate_bounded M)BW HOW)as BOW.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob bound(source_ordinal_predicate_bounded M)Bbeta HOB)as BOB.
 pose proof(source_raw_subset_bounded M w beta subset bound BW Bbeta HSub)as BSub.
 pose proof(source_LL_instance_bounded M beta Lb lb bound Bbeta BLb HLb)as BLB.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HEGoal)as BG.
 apply(source_zfr_finite_rule M[hyLaw;pointLaw][witness;lk;block;ow;ob;subset;lb]goal law bound).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];assumption.
 - exact BG.
 - exact HLaw.
 - intros f[<-|[<-|[]]];assumption.
 - intros gb gc gn HC Laws Premises.
   assert(PEx:source_full_prv M gb gc gn ex).
   { apply(source_full_finite_telescope_apply M[ow;ob;subset;lb]ex hyLaw HTel gb gc gn(Laws hyLaw ltac:(cbn;tauto))).
     intros f[<-|[<-|[<-|[<-|[]]]]];apply Premises;cbn;tauto. }
   apply(source_full_finite_telescope_apply M[witness;lk;block;ex]goal pointLaw HPointLaw gb gc gn(Laws pointLaw ltac:(cbn;tauto))).
   intros f[<-|[<-|[<-|[<-|[]]]]];try(apply Premises;cbn;tauto). exact PEx.
Qed.
Print Assumptions source_PH_raw_subset_functional.
Print Assumptions source_zfr_PH_hierarchy_ordinals.
