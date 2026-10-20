(** Actual full assignment-quantified atomic representation law.
    The An carrier formula remains a genuine antecedent, to be supplied
    by its independent proved existence theorem at the final witness step. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceDefinabilityBounds SourceDefinabilityIteration SourceFiniteCutoffShift SourceQfFunctionality SourceQuantifierRules NumericalInstantiation
 SourceRepresentativeRenaming SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierReopen SourceRepresentationRecipe
 SourceAtomicRecipe SourceAtomicCondition SourceAtomicPoint SourceAtomicPointParts SourceAtomicReverseIndices SourceAtomicDnMap SourceAtomicOperationSyntax
 SourceIffGraphs SourceEnvFDomainWitnessBounds SourceRepresentationPaddedDn SourceRepresentationPadding SourceRepresentationConjunctionDn
 SourceDescriptorConditionalPlain SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceDn.
Unset Implicit Arguments.
Theorem source_zfr_atomic_representation_law M(member:bool)count i j ki kj phi rep carrier namedCarrier numI numJ condition:
 source_bounded M phi count->sf_relation M(if member then SFMember else SFEqual)i j phi->
 source_reverse_index M count i ki->source_reverse_index M count j kj->source_numf M ki numI->source_numf M kj numJ->
 source_representation_recipe M count phi rep->source_environment_carrier_recipe M count carrier->
 source_representative_renaming M(code_numeral M 2)carrier namedCarrier->source_atomic_condition M member numI numJ condition->
 exists inner result,sf_relation M SFImpl namedCarrier rep inner/\sf_relation M SFImpl condition inner result/\source_zfr_provable M result.
Proof.
 intros BPhi HAtom HI HJ HNumI HNumJ HRep HCarrier HNamed HCondition.
 destruct(source_representation_atomic_shape M count member i j phi rep HAtom HRep)
  as(environment&first&guard&atom&point&HE&H1&H2&HA&HP&HD).
 destruct(source_environment_carrier_reopen M count carrier namedCarrier HCarrier HNamed)
  as(environment'&first'&guard'&basepoint&memCarrier&oldinner&oldpoint&HE'&H1'&H2'&HBase&HDBase&HMemCarrier&HOldInner&HOldPoint&HPointRename&HDOld).
 assert(E:environment'=environment)by(eapply source_def_iteration_functional;eassumption). subst environment'.
 assert(E:first'=first)by(eapply source_cutoff_shift_functional;eassumption). subst first'.
 assert(E:guard'=guard)by(eapply source_cutoff_shift_functional;eassumption). subst guard'.
 destruct(source_representation_point_parts M guard atom point HP)as(memRepresentative&equiv&newinner&HMemRepresentative&HIff&HNewInner&HPoint).
 pose proof(source_numf_bound M ki numI HNumI)as BI.
 pose proof(source_numf_bound M kj numJ HNumJ)as BJ.
 destruct(source_atomic_condition_padding_shift M count member numI numJ condition BI BJ HCondition)
  as(padded&shifted&HConditionPadded&HConditionShifted&HPad&HShift).
 destruct HConditionShifted as(ni&nj&op&nums&HNI&HNJ&HOp&HNums&HShiftedCondition).
 destruct(source_zfr_atomic_representation_point M member count i j ki kj environment first guard numI numJ
  (succM M(succM M(succM M(succM M count))))(succM M(succM M(succM M(succM M(succM M count)))))ni nj
  (succM M(succM M(succM M count)))(code_numeral M 1)op memCarrier atom memRepresentative equiv
  HI HJ HE HNumI HNumJ H1 H2 HNI HNJ HOp HMemCarrier HA HMemRepresentative HIff)
  as(nums'&shifted'&oldinner'&newinner'&pointmap&pointproof&HNums'&HShiftedCondition'&HOldInner'&HNewInner'&HPointMap&HPointProof&PPoint).
 assert(E:nums'=nums)by(eapply sf_relation_functional;eassumption). subst nums'.
 assert(E:shifted'=shifted)by(eapply sf_relation_functional;eassumption). subst shifted'.
 assert(E:oldinner'=oldinner)by(eapply sf_relation_functional;eassumption). subst oldinner'.
 assert(E:newinner'=newinner)by(eapply sf_relation_functional;eassumption). subst newinner'.
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)H1)as BFirst.
 pose proof(source_cutoff_shift_bounded M 1 first guard(succM M count)BFirst H2)as BGuard.
 assert(BAtom:source_bounded M atom(succM M(succM M(succM M count)))).
 { destruct member.
   - destruct(proj1(source_bounded_accept_atom M SFMember i j phi count(or_introl eq_refl)HAtom)BPhi)as(Bi&Bj).
     apply(proj2(source_bounded_accept_atom M SFMember _ _ atom _(or_introl eq_refl)HA)). split;do 3 apply coding_lt_succ_cancel;assumption.
   - destruct(proj1(source_bounded_accept_atom M SFEqual i j phi count(or_intror eq_refl)HAtom)BPhi)as(Bi&Bj).
     apply(proj2(source_bounded_accept_atom M SFEqual _ _ atom _(or_intror eq_refl)HA)). split;do 3 apply coding_lt_succ_cancel;assumption. }
 assert(BMemRepresentative:source_bounded M memRepresentative(succM M(succM M(succM M count)))).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ memRepresentative _(or_introl eq_refl)HMemRepresentative)).
   split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel,coding_zero_lt_succ]. }
 pose proof(source_iff_bounded M memRepresentative atom equiv _ BMemRepresentative BAtom HIff)as BIff.
 pose proof(proj2(source_bounded_accept_binary M SFImpl guard equiv newinner _(or_intror(or_intror eq_refl))HNewInner)(conj BGuard BIff))as BNewInner.
 assert(BMemCarrier:source_bounded M memCarrier(succM M(succM M(succM M(succM M count))))).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ memCarrier _(or_introl eq_refl)HMemCarrier)). split;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
 pose proof(proj2(source_bounded_accept_binary M SFImpl guard memCarrier oldinner _(or_intror(or_intror eq_refl))HOldInner)
  (conj(ew_raise_bound M guard _ BGuard)BMemCarrier))as BOldInner.
 set(K:=succM M(succM M(succM M(succM M(succM M(succM M count)))))).
 assert(BOldWide:source_bounded M oldinner(succM M K)).
 { exact(ew_raise_bound M oldinner _(ew_raise_bound M oldinner _(ew_raise_bound M oldinner _ BOldInner))). }
 pose proof(conjunction_hole_bound M count newinner BNewInner)as BNewWide.
 rewrite(Arithmetic.add_comm M count(code_numeral M 6))in BNewWide.
 change(source_bounded M newinner(succM M(addM M(succM M(succM M(succM M(succM M(succM M(succM M(zeroM M)))))))count)))in BNewWide.
 rewrite!Arithmetic.add_succ,Arithmetic.add_zero in BNewWide.
 change(source_bounded M newinner(succM M K))in BNewWide.
 pose proof(source_atomic_condition_bound M member numI numJ condition BI BJ HCondition)as BC.
 pose proof(source_representation_padding_bounded M count condition padded(code_numeral M 5)BC HPad)as BPad.
 assert(BPadWide:source_bounded M padded K).
 { change(source_bounded M padded(succM M(succM M(succM M(succM M(succM M(succM M count))))))).
   rewrite(Arithmetic.add_comm M count(code_numeral M 5))in BPad.
   change(source_bounded M padded(addM M(succM M(succM M(succM M(succM M(succM M(zeroM M))))))count))in BPad.
   rewrite!Arithmetic.add_succ,Arithmetic.add_zero in BPad. exact(ew_raise_bound M padded _ BPad). }
 destruct(sf_relation_total M SFImpl oldpoint point)as(allmap&HAllMap).
 destruct(sf_relation_total M SFImpl padded allmap)as(allproof&HAllProof).
 pose proof(source_descriptor_conditional_universal_plain M ZFRSourceDescriptor padded shifted oldinner newinner pointmap pointproof
  oldpoint point allmap allproof K BPadWide HShift BOldWide BNewWide HPointMap HPointProof HOldPoint HPoint HAllMap HAllProof
  (proj2(source_zfr_descriptor_provable M pointproof)PPoint))as PAll.
 destruct(sf_relation_total M SFImpl namedCarrier rep)as(inner&HInner).
 destruct(sf_relation_total M SFImpl condition inner)as(result&HResult).
 exists inner,result. refine(conj HInner(conj HResult _)).
 apply(source_zfr_dn_padded_unary_map M count condition padded oldpoint point namedCarrier rep allmap allproof inner result(code_numeral M 4)).
 - exact(ew_raise_bound M condition _ BC).
 - rewrite(Arithmetic.add_comm M count(succM M(succM M(code_numeral M 4)))).
   change(source_bounded M oldpoint(addM M(succM M(succM M(succM M(succM M(succM M(succM M(zeroM M)))))))count)).
   rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
   exact(proj2(source_bounded_accept_unary M SFAll oldinner oldpoint K(or_introl eq_refl)HOldPoint)BOldWide).
 - rewrite(Arithmetic.add_comm M count(succM M(succM M(code_numeral M 4)))).
   change(source_bounded M point(addM M(succM M(succM M(succM M(succM M(succM M(succM M(zeroM M)))))))count)).
   rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
   exact(proj2(source_bounded_accept_unary M SFAll newinner point K(or_introl eq_refl)HPoint)BNewWide).
 - exact HPad.
 - exact HDOld.
 - exact HD.
 - exact HAllMap.
 - exact HAllProof.
 - exact HInner.
 - exact HResult.
 - exact(proj1(source_zfr_descriptor_provable M allproof)PAll).
Qed.
Print Assumptions source_zfr_atomic_representation_law.
