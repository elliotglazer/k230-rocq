(** Put the proved quantified atom law in a fixed hygienic witness frame:
    carrierA1, environment-carrierAn3, indices4/5, representativeR0. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceAtomicReverseIndices SourceAtomicCondition SourceAtomicRepresentationLaw SourceRepresentationRecipe
 SourceEnvironmentCarrierRecipe SourceRepresentativeRenaming SourceFiniteNameParameters NumericalRenamingMaps NumericalRenaming
 SourceRenamingIdentity SourceShiftSpecialization SourceRenamingDiamond SourceQuantifierRules SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_zfr_atomic_named_law M(member:bool)count i j ki kj phi rep carrier numI numJ:
 source_bounded M phi count->sf_relation M(if member then SFMember else SFEqual)i j phi->
 source_reverse_index M count i ki->source_reverse_index M count j kj->SourceDefinabilityBounds.source_numf M ki numI->SourceDefinabilityBounds.source_numf M kj numJ->
 source_representation_recipe M count phi rep->source_environment_carrier_recipe M count carrier->
 exists namedCarrier condition inner result,
 source_representative_renaming M(code_numeral M 3)carrier namedCarrier/\
 source_atomic_condition_names M member numI numJ(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(zeroM M)condition/\
 sf_relation M SFImpl namedCarrier rep inner/\sf_relation M SFImpl condition inner result/\source_zfr_provable M result.
Proof.
 intros BPhi HAtom HI HJ HNumI HNumJ HRep HCarrier.
 destruct(source_representative_renaming_total M(code_numeral M 2)carrier)as(oldCarrier&HOldCarrier).
 destruct(source_atomic_condition_names_total M member numI numJ(code_numeral M 2)(code_numeral M 3)(code_numeral M 4)(zeroM M))as(oldCondition&HOldCondition).
 destruct(source_zfr_atomic_representation_law M member count i j ki kj phi rep carrier oldCarrier numI numJ oldCondition
  BPhi HAtom HI HJ HNumI HNumJ HRep HCarrier HOldCarrier HOldCondition)as(oldInner&oldResult&HOldInner&HOldResult&POld).
 destruct(source_representative_renaming_total M(code_numeral M 3)carrier)as(namedCarrier&HNamedCarrier).
 destruct(source_atomic_condition_names_total M member numI numJ(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(zeroM M))as(condition&HCondition).
 destruct(sf_relation_total M SFImpl namedCarrier rep)as(inner&HInner).
 destruct(sf_relation_total M SFImpl condition inner)as(result&HResult).
 set(names:=fun idx:nat=>match idx with 0=>zeroM M|1=>code_numeral M 1|2=>code_numeral M 3|3=>code_numeral M 4|_=>code_numeral M 5 end).
 destruct(source_finite_names_total M 5 names(zeroM M))as(rb&rc&HMap).
 assert(HZero:renaming_lookup M rb rc(code_numeral M 5)(zeroM M)(zeroM M)(zeroM M))by(exact(HMap 0 ltac:(lia))).
 assert(HOne:renaming_lookup M rb rc(code_numeral M 5)(zeroM M)(code_numeral M 1)(code_numeral M 1))by(exact(HMap 1 ltac:(lia))).
 assert(RCondition:numerical_renaming M oldCondition rb rc(code_numeral M 5)(zeroM M)condition).
 { exact(source_atomic_condition_names_renaming M member numI numJ _ _ _ _ oldCondition _ _ _ _ condition rb rc(code_numeral M 5)(zeroM M)
   (SourceDefinabilityBounds.source_numf_bound M ki numI HNumI)(SourceDefinabilityBounds.source_numf_bound M kj numJ HNumJ)
   HOldCondition HCondition(HMap 2 ltac:(lia))(HMap 3 ltac:(lia))(HMap 4 ltac:(lia))HZero). }
 pose proof(source_environment_carrier_recipe_bounded M count carrier HCarrier)as BCarrier.
 assert(RCarrier:numerical_renaming M oldCarrier rb rc(code_numeral M 5)(zeroM M)namedCarrier).
 { assert(HIdentity:numerical_renaming M carrier(zeroM M)(zeroM M)(zeroM M)(zeroM M)carrier).
   { apply(numerical_renaming_identity_on_bound M carrier _ _ _ _(code_numeral M 2)BCarrier). intros idx _. apply source_empty_renaming_lookup. }
   apply(numerical_source_renaming_diamond M carrier(code_numeral M 2)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)(code_numeral M 2)(code_numeral M 2)(code_numeral M 1)(zeroM M)
    (code_numeral M 3)(code_numeral M 3)(code_numeral M 1)(zeroM M)rb rc(code_numeral M 5)(zeroM M)
    carrier oldCarrier namedCarrier BCarrier HIdentity HOldCarrier HNamedCarrier).
   intros idx v l w HIdx HV HW HOld.
   pose proof(renaming_lookup_functional M _ _ _ _ idx v idx HV(source_empty_renaming_lookup M idx))as E. subst v.
   destruct(source_numeral_initial_segment M 2 idx HIdx)as(ix&Hix&E). subst idx.
   destruct ix as[|[|ix]];try lia.
   - pose proof(renaming_lookup_functional M _ _ _ _(zeroM M)l(code_numeral M 2)HOld(representative_lookup_zero M(code_numeral M 2)))as E. subst l.
     pose proof(renaming_lookup_functional M _ _ _ _(zeroM M)w(code_numeral M 3)HW(representative_lookup_zero M(code_numeral M 3)))as E. subst w.
     exact(HMap 2 ltac:(lia)).
   - pose proof(renaming_lookup_functional M _ _ _ _(code_numeral M 1)l(code_numeral M 1)HOld
       (representative_lookup_nonzero M(code_numeral M 2)(code_numeral M 1)ltac:(intro E;exact(Model.zero_ne_succ M(zeroM M)(eq_sym E)))))as E. subst l.
     pose proof(renaming_lookup_functional M _ _ _ _(code_numeral M 1)w(code_numeral M 1)HW
       (representative_lookup_nonzero M(code_numeral M 3)(code_numeral M 1)ltac:(intro E;exact(Model.zero_ne_succ M(zeroM M)(eq_sym E)))))as E. subst w.
     exact HOne. }
 assert(RRep:numerical_renaming M rep rb rc(code_numeral M 5)(zeroM M)rep).
 { apply(numerical_renaming_identity_on_bound M rep _ _ _ _(code_numeral M 2)(source_representation_recipe_bounded M count phi rep BPhi HRep)).
   intros idx HIdx. destruct(source_numeral_initial_segment M 2 idx HIdx)as(ix&Hix&E). subst idx.
   destruct ix as[|[|ix]];try lia;assumption. }
 assert(RInner:numerical_renaming M oldInner rb rc(code_numeral M 5)(zeroM M)inner).
 { apply(proj2(numerical_renaming_binary M SFImpl oldCarrier rep oldInner rb rc(code_numeral M 5)(zeroM M)inner
    (or_intror(or_intror eq_refl))HOldInner)). exists namedCarrier,rep. repeat split;assumption. }
 assert(RResult:numerical_renaming M oldResult rb rc(code_numeral M 5)(zeroM M)result).
 { apply(proj2(numerical_renaming_binary M SFImpl oldCondition oldInner oldResult rb rc(code_numeral M 5)(zeroM M)result
    (or_intror(or_intror eq_refl))HOldResult)). exists condition,inner. repeat split;assumption. }
 exists namedCarrier,condition,inner,result. refine(conj HNamedCarrier(conj HCondition(conj HInner(conj HResult _)))).
 apply(proj1(source_zfr_descriptor_provable M result)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor oldResult rb rc(code_numeral M 5)(zeroM M)result
  (proj2(source_zfr_descriptor_provable M oldResult)POld)RResult).
Qed.
Print Assumptions source_zfr_atomic_named_law.
