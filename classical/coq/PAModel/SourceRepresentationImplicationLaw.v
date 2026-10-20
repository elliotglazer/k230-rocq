(** Actual constructor law for implication representation. The auxiliary
    assignment carrier is kept as a genuine third representative premise. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceRepresentationRecipe SourceRepresentationBinaryChildren SourceRepresentationRecipeBounds
 SourceRepresentationPointCompatibility SourceRepresentationNamedRecipe SourceRepresentationNamedPoint
 SourceImplicationPointCompatibility SourceImplicationFrame SourceImplicationDn SourceCarrierPointReopen
 SourceEnvironmentCarrierRecipe SourceRepresentativeRenaming SourceDefinabilityBounds SourceFiniteCutoffShift
 SetSchemaConstructors SourceDescriptorProvability FixedSourceBounds SourceRepresentationDifferenceProgram SourceRepresentationDifferencePoints
 SourceImplicationDifferenceProgram SourceImplicationDifferenceUniversal SourceImplicationDifferencePoints SourcePropositionalTemplates SourceDn.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_representation_implication_law M T count left right implication result:
 source_bounded M implication count->sf_relation M SFImpl left right implication->
 source_representation_recipe M count implication result->
 exists repLeft repRight carrier namedLeft namedRight namedCarrier operation1 operation2 condition inner body all law,
 source_representation_recipe M count left repLeft/\source_representation_recipe M count right repRight/\
 source_environment_carrier_recipe M count carrier/\
 source_representative_renaming M(code_numeral M 3)repLeft namedLeft/\
 source_representative_renaming M(code_numeral M 4)repRight namedRight/\
 source_representative_renaming M(code_numeral M 6)carrier namedCarrier/\
 code_relation M(implication_outer_environment M)E_double_difference_first_operation operation1/\
 code_relation M(implication_outer_environment M)E_implication_difference_second_operation operation2/\
 sf_relation M SFAnd operation1 operation2 condition/\sf_relation M SFImpl namedRight result inner/\
 sf_relation M SFImpl namedLeft inner body/\sf_relation M SFImpl namedCarrier body all/\
 sf_relation M SFImpl condition all law/\source_descriptor_provable M T law.
Proof.
 intros HB HImpl HRecipe.
 destruct(proj1(source_bounded_accept_binary M SFImpl left right implication count(or_intror(or_intror eq_refl))HImpl)HB)as[BL BR].
 destruct(source_representation_binary_children M count SFImpl left right implication result(or_intror(or_intror eq_refl))HImpl HRecipe)
  as(env&first&guard&ml&mr&rl&rr&rc&pl&pr&pc&repL&repR&HE&H1&H2&HML&HMR&HRL&HRR&HRelImpl&HPL&HPR&HPC&HDL&HDR&HDC&HLRecipe&HRRecipe).
 destruct(source_representative_renaming_total M(code_numeral M 3)repL)as(namedL&HNamedL).
 destruct(source_representative_renaming_total M(code_numeral M 4)repR)as(namedR&HNamedR).
 assert(N3:~coding_lt M(code_numeral M 3)(code_numeral M 2))by(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 2))in H;lia).
 assert(N4:~coding_lt M(code_numeral M 4)(code_numeral M 2))by(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 2))in H;lia).
 assert(N6:~coding_lt M(code_numeral M 6)(code_numeral M 2))by(intro H;apply(proj1(fixed_source_numeral_lt_iff M 6 2))in H;lia).
 destruct(source_representation_point_reopen M count left env first guard ml rl pl repL(code_numeral M 3)namedL
  BL HE H1 H2 HML HRL HPL HDL N3 HNamedL)as(pointL&HPointL&HDNamedL).
 destruct(source_representation_point_reopen M count right env first guard mr rr pr repR(code_numeral M 4)namedR
  BR HE H1 H2 HMR HRR HPR HDR N4 HNamedR)as(pointR&HPointR&HDNamedR).
 destruct(code_relation_total M E_environment_carrier_point(fun _=>guard))as(pa&HPA).
 destruct(source_dn_total M count pa)as(carrier&HCarrierDn).
 assert(HCarrier:source_environment_carrier_recipe M count carrier).
 { exists env,first,guard,pa. exact(conj HE(conj H1(conj H2(conj HPA HCarrierDn)))). }
 destruct(source_representative_renaming_total M(code_numeral M 6)carrier)as(namedA&HNamedA).
 destruct(source_carrier_point_reopen M count env first guard pa carrier(code_numeral M 6)namedA HE H1 H2 HPA HCarrierDn N6 HNamedA)
  as(member&carrierInner&coverage&HMember&HCarrierInner&HCarrierAll&HCarrierPoint&HDNamedA).
 set(rho:=implication_point_environment M count rl rr guard).
 assert(GLeft:code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))pointL).
 { change(code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))pointL).
   exact(proj2(representation_named_first_point M rho pointL)HPointL). }
 assert(GRight:code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))pointR).
 { change(code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))pointR).
   exact(proj2(representation_named_second_point M rho pointR)HPointR). }
 assert(GTarget:code_relation M rho(E_implication_difference_all implication_difference_conclusion)pc).
 { apply(proj2(representation_named_implication_point M rho rc pc HRelImpl)).
   exact(proj1(representation_standard_point_graph M guard rc pc)HPC). }
 assert(GCoverage:code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTSlot 7)))coverage).
 { exact(representation_implication_carrier_point M rho member carrierInner coverage HMember HCarrierInner HCarrierAll). }
 pose proof(source_representation_relative_bound M count left ml rl BL HML HRL)as BRL.
 pose proof(source_representation_relative_bound M count right mr rr BR HMR HRR)as BRR.
 pose proof(source_cutoff_shift_bounded M 1 env first count(source_envf_bound M count env HE)H1)as BF.
 pose proof(source_cutoff_shift_bounded M 1 first guard(succM M count)BF H2)as BG.
 destruct(source_descriptor_canonical_implication_dn M T count rl rr guard coverage pointL pointR pc namedA namedL namedR result
  BRL BRR BG GCoverage GLeft GRight GTarget HDNamedA HDNamedL HDNamedR HDC)
  as(op1&op2&condition&inner&body&all&law&HO1&HO2&HCondition&HInner&HBody&HAll&HLaw&PLaw).
 exists repL,repR,carrier,namedL,namedR,namedA,op1,op2,condition,inner,body,all,law.
 exact(conj HLRecipe(conj HRRecipe(conj HCarrier(conj HNamedL(conj HNamedR(conj HNamedA(conj HO1(conj HO2(conj HCondition(conj HInner(conj HBody(conj HAll(conj HLaw PLaw))))))))))))).
Qed.
Print Assumptions source_representation_implication_law.
