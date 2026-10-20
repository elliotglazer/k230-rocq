(** Move the pure An2 role to An4 before adding the closure container C2.
    No closure witness is consumed by this proof-renaming calculation. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded FixedSourceBounds
 SourceNumeralLift SourceRepresentativeRenaming SourceShiftSpecialization SourceRenamingIdentity SourceRenamingDiamond NumericalRenamingMaps NumericalRenaming
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterRenamingTransport SourceProjectionOperationPadding SourceProjectionFiniteSyntax
 SourceProjectionDnConstructor SourceProjectionProfilePoint SourceRepresentationRecipe SourceEnvironmentCarrierRecipe SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition projection_witness_roles M i:=code_numeral M(match i with 0=>0|1=>1|_=>4 end).
Theorem source_projection_witness_map_total M:exists b c,
 (forall i,(i<3)%nat->renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M i)(projection_witness_roles M i)).
Proof. exact(source_finite_names_total M 3(projection_witness_roles M)(zeroM M)). Qed.
Theorem source_projection_representative_image M f named renamed b c r s:
 source_bounded M f(code_numeral M 2)->source_representative_renaming M r f named->source_representative_renaming M s f renamed->
 renaming_lookup M b c(code_numeral M 3)(zeroM M)r s->
 renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 1)(code_numeral M 1)->
 numerical_renaming M named b c(code_numeral M 3)(zeroM M)renamed.
Proof.
 intros BF HN HR HRS HOne.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _(code_numeral M 2)BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f(code_numeral M 2)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)r r(code_numeral M 1)(zeroM M)
  s s(code_numeral M 1)(zeroM M)b c(code_numeral M 3)(zeroM M)f named renamed BF HId HN HR).
 intros i j l m HI HJ HM HL.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HM.
 destruct(source_numeral_initial_segment M 2 i HI)as(index&HIndex&->).
 destruct index as[|[|index]];try lia.
 - rewrite(renaming_lookup_functional M _ _ _ _ _ l r HL(representative_lookup_zero M r)).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m s HM(representative_lookup_zero M s)). exact HRS.
 - rewrite(renaming_lookup_functional M _ _ _ _ _ l _ HL(representative_lookup_nonzero M r _ (fun E=>Model.zero_ne_succ M(zeroM M)(eq_sym E)))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(representative_lookup_nonzero M s _ (fun E=>Model.zero_ne_succ M(zeroM M)(eq_sym E)))). exact HOne.
Qed.
Theorem source_zfr_projection_witness_roles M count f existential rep childrep namedchild carrier namedcarrier:
 source_bounded M existential count->sf_relation M SFEx f(zeroM M)existential->
 source_representation_recipe M count existential rep->source_representation_recipe M(succM M count)f childrep->
 source_representative_renaming M(code_numeral M 3)childrep namedchild->source_environment_carrier_recipe M count carrier->
 source_representative_renaming M(code_numeral M 4)carrier namedcarrier->
 exists op inner body law,
 code_relation M(projection_five_values(code_numeral M 4)(code_numeral M 3)(code_numeral M 1)(zeroM M)(zeroM M))
  (source_parameter_expression(source_finite_parameter_names 4)projection_operation4)op /\
 sf_relation M SFImpl namedcarrier rep inner/\sf_relation M SFImpl namedchild inner body/\sf_relation M SFImpl op body law/\source_zfr_provable M law.
Proof.
 intros BEx HEx HR HChild HChildName HCarrier HCarrierName.
 destruct(source_representative_renaming_total M(code_numeral M 2)carrier)as(oldcarrier&HOldCarrier).
 destruct(source_zfr_projection_dn_constructor M count f existential rep childrep namedchild carrier oldcarrier BEx HEx HR HChild HChildName HCarrier HOldCarrier)
  as(oldop&oldinner&oldbody&oldlaw&HOldOp&HOldInner&HOldBody&HOldLaw&POldLaw).
 destruct(source_projection_witness_map_total M)as(b&c&HNames).
 pose proof(HNames 1 ltac:(lia))as HOne.
 assert(HTwo:renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 2)(code_numeral M 4))by(exact(HNames 2 ltac:(lia))).
 assert(HThree:renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 3)(code_numeral M 3)).
 { apply(proj2(renaming_lookup_outside M b c(code_numeral M 3)(zeroM M)_ _
   ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia))). symmetry. apply coding_add_zero_r. }
 pose proof(proj1(source_bounded_accept_unary M SFEx f existential count(or_intror eq_refl)HEx)BEx)as BF.
 pose proof(source_projection_representative_image M carrier oldcarrier namedcarrier b c(code_numeral M 2)(code_numeral M 4)
  (source_environment_carrier_recipe_bounded M count carrier HCarrier)HOldCarrier HCarrierName HTwo HOne)as HCarrierImage.
 pose proof(source_projection_representative_image M childrep namedchild namedchild b c(code_numeral M 3)(code_numeral M 3)
  (source_representation_recipe_bounded M(succM M count)f childrep BF HChild)HChildName HChildName HThree HOne)as HChildImage.
 assert(HRepImage:numerical_renaming M rep b c(code_numeral M 3)(zeroM M)rep).
 { apply(numerical_renaming_identity_on_bound M rep _ _ _ _(code_numeral M 2)(source_representation_recipe_bounded M count existential rep BEx HR)).
   intros i HI. destruct(source_numeral_initial_segment M 2 i HI)as(index&HIndex&->).
   destruct index as[|[|index]];try lia;[exact(HNames 0 ltac:(lia))|exact(HNames 1 ltac:(lia))]. }
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 4)projection_operation4)
  (projection_five_values(code_numeral M 4)(code_numeral M 3)(code_numeral M 1)(zeroM M)(zeroM M)))as(op&HOp).
 assert(HOpImage:numerical_renaming M oldop b c(code_numeral M 3)(zeroM M)op).
 { apply(source_parameter_renaming_transport M 4 projection_operation4 projection_operation_bound(source_finite_parameter_names 4)(source_finite_parameter_names 4)
  (projection_outer_roles M)(projection_five_values(code_numeral M 4)(code_numeral M 3)(code_numeral M 1)(zeroM M)(zeroM M))b c(code_numeral M 3)(zeroM M)oldop op);[|exact HOldOp|exact HOp].
   intros[|[|[|[|i]]]]x y HI HX HY;try lia.
   - change(x=code_numeral M 2)in HX. change(y=code_numeral M 4)in HY. now subst x y.
   - change(x=code_numeral M 3)in HX. change(y=code_numeral M 3)in HY. now subst x y.
   - change(x=code_numeral M 1)in HX. change(y=code_numeral M 1)in HY. now subst x y.
   - change(x=zeroM M)in HX. change(y=zeroM M)in HY. subst x y. exact(HNames 0 ltac:(lia)). }
 destruct(sf_relation_total M SFImpl namedcarrier rep)as(inner&HInner).
 destruct(sf_relation_total M SFImpl namedchild inner)as(body&HBody).
 destruct(sf_relation_total M SFImpl op body)as(law&HLaw).
 assert(HInnerImage:numerical_renaming M oldinner b c(code_numeral M 3)(zeroM M)inner).
 { apply(proj2(numerical_renaming_binary M SFImpl oldcarrier rep oldinner b c(code_numeral M 3)(zeroM M)inner(or_intror(or_intror eq_refl))HOldInner)).
   exists namedcarrier,rep. exact(conj HCarrierImage(conj HRepImage HInner)). }
 assert(HBodyImage:numerical_renaming M oldbody b c(code_numeral M 3)(zeroM M)body).
 { apply(proj2(numerical_renaming_binary M SFImpl namedchild oldinner oldbody b c(code_numeral M 3)(zeroM M)body(or_intror(or_intror eq_refl))HOldBody)).
   exists namedchild,inner. exact(conj HChildImage(conj HInnerImage HBody)). }
 assert(HLawImage:numerical_renaming M oldlaw b c(code_numeral M 3)(zeroM M)law).
 { apply(proj2(numerical_renaming_binary M SFImpl oldop oldbody oldlaw b c(code_numeral M 3)(zeroM M)law(or_intror(or_intror eq_refl))HOldLaw)).
   exists op,body. exact(conj HOpImage(conj HBodyImage HLaw)). }
 exists op,inner,body,law. refine(conj HOp(conj HInner(conj HBody(conj HLaw _)))).
 apply(proj1(source_zfr_descriptor_provable M law)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor oldlaw b c(code_numeral M 3)(zeroM M)law
  (proj2(source_zfr_descriptor_provable M oldlaw)POldLaw)HLawImage).
Qed.
Print Assumptions source_projection_witness_map_total.
Print Assumptions source_projection_representative_image.
Print Assumptions source_zfr_projection_witness_roles.
