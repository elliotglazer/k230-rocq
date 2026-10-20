(** Move the An successor law's auxiliary old carrier from2 to3, leaving
    the new carrier0 and assignment carrier1 fixed. This makes room for
    the external closure container at2. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierStepLaw SourceEnvironmentOperationPadding SourceEnvironmentPointSlots
 SourceFiniteParameters SourceFiniteParameterProofs SourceRepresentativeRenaming SourceRepresentationPadding
 SourceRenamingIdentity SourceShiftSpecialization FixedSourceBounds SourceRenamingDiamond SourceDescriptorProvability SourceDescriptorClosure
 SourceZFRProvability SourceSetTheoryDescriptors NumericalRenaming NumericalRenamingMaps.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_representative_padding_one M f old named:
 source_bounded M f(code_numeral M 2) ->source_representative_renaming M(code_numeral M 2)f old ->
 source_representative_renaming M(code_numeral M 3)f named ->source_representation_padding M(code_numeral M 1)old named.
Proof.
 intros BF HOld HNamed.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _(code_numeral M 2)BF).
   intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f(code_numeral M 2)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (code_numeral M 2)(code_numeral M 2)(code_numeral M 1)(zeroM M)
  (code_numeral M 3)(code_numeral M 3)(code_numeral M 1)(zeroM M)
  (code_numeral M 6)(code_numeral M 2)(code_numeral M 2)(code_numeral M 1)
  f old named BF HId HOld HNamed).
 intros i j l m HI HJ HM HL.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HM.
 destruct(source_numeral_initial_segment M 2 i HI)as(index&HIndex&->).
 destruct index as[|[|index]];try lia.
 - rewrite(renaming_lookup_functional M _ _ _ _ _ l _ HL(representative_lookup_zero M(code_numeral M 2))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(representative_lookup_zero M(code_numeral M 3))).
   pose proof(representation_padding_outside_lookup M(code_numeral M 1)(code_numeral M 2)
    ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 2 2))in H;lia))as H.
   change(representation_padding_lookup M(code_numeral M 1)(code_numeral M 2)
    (addM M(succM M(succM M(zeroM M)))(code_numeral M 1)))in H.
   now rewrite!Arithmetic.add_succ,Arithmetic.add_zero in H.
 - assert(HN:code_numeral M 1<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M(zeroM M)(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ l _ HL(representative_lookup_nonzero M(code_numeral M 2)_ HN)).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(representative_lookup_nonzero M(code_numeral M 3)_ HN)).
   apply representation_padding_one_lookup.
Qed.
Theorem source_zfr_environment_carrier_named_step M count previous result named:
 source_environment_carrier_recipe M count previous ->source_environment_carrier_recipe M(succM M count)result ->
 source_representative_renaming M(code_numeral M 3)previous named ->
 exists op inner law,source_environment_operation_graph M(code_numeral M 3)op /\
 sf_relation M SFImpl named result inner /\sf_relation M SFImpl op inner law /\source_zfr_provable M law.
Proof.
 intros HP HR HNamed. destruct(source_representative_renaming_total M(code_numeral M 2)previous)as(old&HOld).
 destruct(source_zfr_environment_carrier_step_law M count previous result old HP HR HOld)
 as(oldop&oldinner&oldlaw&HOldOp&HOldInner&HOldLaw&POld).
 destruct(code_relation_total M(source_parameter_expression source_three_parameter_names environment_operation_source)
  (environment_operation_roles M(code_numeral M 3)))as(op&HOp).
 pose proof(source_environment_operation_padding M(code_numeral M 1)oldop op HOldOp HOp)as ROp.
 pose proof(source_representative_padding_one M previous old named
  (source_environment_carrier_recipe_bounded M count previous HP)HOld HNamed)as RNamed.
 assert(RResult:source_representation_padding M(code_numeral M 1)result result).
 { apply(numerical_renaming_identity_on_bound M result _ _ _ _(code_numeral M 2)
   (source_environment_carrier_recipe_bounded M(succM M count)result HR)).
   intros i HI. exact(representation_padding_inside_lookup M(code_numeral M 1)i HI). }
 destruct(sf_relation_total M SFImpl named result)as(inner&HInner).
 destruct(sf_relation_total M SFImpl op inner)as(law&HLaw).
 assert(RInner:source_representation_padding M(code_numeral M 1)oldinner inner).
 { apply(proj2(numerical_renaming_binary M SFImpl old result oldinner _ _ _ _ inner(or_intror(or_intror eq_refl))HOldInner)).
   exists named,result. exact(conj RNamed(conj RResult HInner)). }
 assert(RLaw:source_representation_padding M(code_numeral M 1)oldlaw law).
 { apply(proj2(numerical_renaming_binary M SFImpl oldop oldinner oldlaw _ _ _ _ law(or_intror(or_intror eq_refl))HOldLaw)).
   exists op,inner. exact(conj ROp(conj RInner HLaw)). }
 exists op,inner,law. refine(conj HOp(conj HInner(conj HLaw _))).
 apply(proj1(source_zfr_descriptor_provable M law)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor oldlaw _ _ _ _ law
  (proj2(source_zfr_descriptor_provable M oldlaw)POld)RLaw).
Qed.
Print Assumptions source_representative_padding_one.
Print Assumptions source_zfr_environment_carrier_named_step.

