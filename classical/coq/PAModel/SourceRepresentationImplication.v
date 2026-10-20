(** Actual implication case of uniform representation existence.
    Its only proof inputs are the two genuine child induction hypotheses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift FixedSourceBounds
 SourceRepresentationRecipe SourceRepresentationClosureRecipe SourceRepresentationClosureTransport
 SourceRepresentationImplicationLaw SourceRepresentationNamedImplication SourceImplicationFrame
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierClosure SourceEnvironmentCarrierInduction
 SourceNamedClosureWitnessTotal SourceRepresentativeRenaming SourceRepresentationNamedConjunction
 SourceRepresentationDifferencePoints SourceDifferenceNumeralParameters SourceDifferenceProfile
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque code_numeral.
Theorem source_zfr_representation_implication M count left right implication out:
 source_bounded M implication count->sf_relation M SFImpl left right implication->
 (forall child,source_representation_in_closure_recipe M count left child->source_zfr_provable M child)->
 (forall child,source_representation_in_closure_recipe M count right child->source_zfr_provable M child)->
 source_representation_in_closure_recipe M count implication out->source_zfr_provable M out.
Proof.
 intros HB HImpl IHL IHR HOut.
 pose proof HOut as HOutParts. destruct HOutParts as(rep&succ&closure&tbody&tex&middle&HRep&HS&HC&HTB&HTE&HM&HO).
 pose proof(source_representation_closure_graph M count implication rep out HRep HOut)as GOut.
 destruct(proj1(source_bounded_accept_binary M SFImpl left right implication count(or_intror(or_intror eq_refl))HImpl)HB)as[BL BR].
 pose proof(source_representation_recipe_bounded M count implication rep HB HRep)as BRep.
 destruct(source_representation_implication_law M ZFRSourceDescriptor count left right implication rep HB HImpl HRep)
  as(repL&repR&carrier&namedL&namedR&namedA&op1&op2&condition&inner&body&all&law&HRL&HRR&HCarrier&HNL&HNR&HNA&HOp1&HOp2&HCondition&HInner&HBody&HAll&HLaw&PLaw).
 pose proof(source_representation_recipe_bounded M count left repL BL HRL)as BRepL.
 pose proof(source_representation_recipe_bounded M count right repR BR HRR)as BRepR.
 pose proof(source_environment_carrier_recipe_bounded M count carrier HCarrier)as BCarrier.
 pose proof(implication_first_operation_parameters M(implication_outer_environment M)op1 HOp1)as HFirst.
 pose proof(implication_second_operation_parameters M(implication_outer_environment M)op2 HOp2)as HSecond.
 assert(op1=RNC_operation1 M)by(exact(code_relation_functional M _ _ op1 _ HFirst(source_difference_operation_numeral_graph M 3 4 5))). subst op1.
 assert(op2=IWN_operation2 M)by(exact(code_relation_functional M _ _ op2 _ HSecond(source_difference_operation_numeral_graph M 6 5 0))). subst op2.
 destruct(source_representation_in_closure_recipe_total M count left)as(canL&HCanL).
 pose proof(IHL canL HCanL)as PCanL.
 pose proof(source_representation_closure_graph M count left repL canL HRL HCanL)as GCanL.
 destruct(source_zfr_named_closure_witness_total M repL canL(code_numeral M 3)namedL BRepL GCanL PCanL
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia)HNL)
  as(memL&ml&el&outL&HMemL&HML&HEL&GL&PL).
 assert(memL=RNC_member M 3)by(exact(sf_relation_functional M SFMember(code_numeral M 3)(code_numeral M 2)memL(RNC_member M 3)HMemL(sf_make_numeral M SFMember 3 2))). subst memL.
 destruct(source_representation_in_closure_recipe_total M count right)as(canR&HCanR).
 pose proof(IHR canR HCanR)as PCanR.
 pose proof(source_representation_closure_graph M count right repR canR HRR HCanR)as GCanR.
 destruct(source_zfr_named_closure_witness_total M repR canR(code_numeral M 4)namedR BRepR GCanR PCanR
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia)HNR)
  as(memR&mr&er&outR&HMemR&HMR&HER&GR&PR).
 assert(memR=RNC_member M 4)by(exact(sf_relation_functional M SFMember(code_numeral M 4)(code_numeral M 2)memR(RNC_member M 4)HMemR(sf_make_numeral M SFMember 4 2))). subst memR.
 destruct(source_environment_carrier_closure_statement_total M carrier)as(canA&GCanA).
 pose proof(source_zfr_environment_carrier_uniform M count carrier canA HCarrier GCanA)as PCanA.
 destruct(source_zfr_named_closure_witness_total M carrier canA(code_numeral M 6)namedA BCarrier GCanA PCanA
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 6 3))in H;lia)HNA)
  as(memA&ma&ea&outA&HMemA&HMA&HEA&GA&PA).
 assert(memA=RNC_member M 6)by(exact(sf_relation_functional M SFMember(code_numeral M 6)(code_numeral M 2)memA(RNC_member M 6)HMemA(sf_make_numeral M SFMember 6 2))). subst memA.
 destruct(source_zfr_named_implication_from_point M repL repR carrier namedL namedR namedA rep condition inner body all law ml mr ma el er ea outL outR outA
  BRepL BRepR BCarrier BRep HNL HNR HNA HCondition HInner HBody HAll HLaw(proj1(source_zfr_descriptor_provable M law)PLaw)
  HML HMR HMA HEL HER HEA GL PL GR PR GA PA)as(mt&et&namedout&HMT&HET&GNamed&PNamed).
 exact(source_zfr_named_representation_closure M rep mt et namedout out BRep GOut HMT HET GNamed PNamed).
Qed.
Print Assumptions source_zfr_representation_implication.
