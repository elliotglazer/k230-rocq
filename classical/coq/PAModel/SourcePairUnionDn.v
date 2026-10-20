(** Actual pair/union representation law through internally many Dn binders. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
 SourceBounded SourceRepresentationConjunctionFrame SourceRepresentationConjunctionDn SourceRepresentationPointBounds
 SourceRepresentationDifferencePoints SourcePairUnionFrame SourcePairUnionPoint SourcePairUnionProgram
 SourceRepresentationPadding SourceDn SourceDnPaddedBinaryMap SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_pair_union_conditions_total M count left right guard:
 exists pair union condition pair' union' padded,
 code_relation M(conjunction_outer_environment M)E_pair_union_pair pair /\
 code_relation M(conjunction_outer_environment M)E_pair_union_union union /\sf_relation M SFAnd pair union condition /\
 code_relation M(conjunction_point_environment M count left right guard)E_pair_union_pair pair' /\
 code_relation M(conjunction_point_environment M count left right guard)E_pair_union_union union' /\
 sf_relation M SFAnd pair' union' padded /\source_representation_padding M count condition padded /\
 source_bounded M condition(code_numeral M 6) /\source_bounded M padded(addM M count(code_numeral M 6)).
Proof.
 set(outer:=conjunction_outer_environment M). set(inner:=conjunction_point_environment M count left right guard).
 destruct(code_relation_total M E_pair_union_pair outer)as(pair&HP).
 destruct(code_relation_total M E_pair_union_union outer)as(union&HU).
 destruct(sf_relation_total M SFAnd pair union)as(condition&HC).
 destruct(code_relation_total M E_pair_union_pair inner)as(pair'&HP').
 destruct(code_relation_total M E_pair_union_union inner)as(union'&HU').
 destruct(sf_relation_total M SFAnd pair' union')as(padded&HPad).
 exists pair,union,condition,pair',union',padded.
 refine(conj HP(conj HU(conj HC(conj HP'(conj HU'(conj HPad(conj _ (conj _ _)))))))).
 - exact(source_pair_union_condition_padding M count outer inner pair union condition pair' union' padded
    (conjunction_point_names_padding M count left right guard)HP HU HP' HU' HC HPad).
 - apply(proj2(source_bounded_accept_binary M SFAnd pair union condition(code_numeral M 6)(or_introl eq_refl)HC)).
   exact(conj(pair_union_parameter_bound M pair_union_pair_source outer(code_numeral M 6)pair pair_union_pair_bound(conjunction_outer_names_bound M)HP)
    (pair_union_parameter_bound M pair_union_union_source outer(code_numeral M 6)union pair_union_union_bound(conjunction_outer_names_bound M)HU)).
 - apply(proj2(source_bounded_accept_binary M SFAnd pair' union' padded(addM M count(code_numeral M 6))(or_introl eq_refl)HPad)).
   exact(conj(pair_union_parameter_bound M pair_union_pair_source inner(addM M count(code_numeral M 6))pair' pair_union_pair_bound
    (conjunction_point_names_bound M count left right guard)HP')
    (pair_union_parameter_bound M pair_union_union_source inner(addM M count(code_numeral M 6))union' pair_union_union_bound
     (conjunction_point_names_bound M count left right guard)HU')).
Qed.
Theorem source_zfr_canonical_pair_union_dn M count left right guard point1 point2 target rep1 rep2 repTarget:
 source_bounded M left(succM M(succM M(succM M count))) ->
 source_bounded M right(succM M(succM M(succM M count))) ->
 source_bounded M guard(succM M(succM M(succM M count))) ->
 code_relation M(conjunction_point_environment M count left right guard)(E_double_difference_all pair_union_left_template)point1 ->
 code_relation M(conjunction_point_environment M count left right guard)(E_double_difference_all pair_union_right_template)point2 ->
 code_relation M(conjunction_point_environment M count left right guard)(E_double_difference_all pair_union_conclusion)target ->
 source_dn M count point1 rep1 ->source_dn M count point2 rep2 ->source_dn M count target repTarget ->
 exists pair union condition inner body law,
 code_relation M(conjunction_outer_environment M)E_pair_union_pair pair /\
 code_relation M(conjunction_outer_environment M)E_pair_union_union union /\sf_relation M SFAnd pair union condition /\
 sf_relation M SFImpl rep2 repTarget inner /\sf_relation M SFImpl rep1 inner body /\
 sf_relation M SFImpl condition body law /\source_zfr_provable M law.
Proof.
 intros BL BR BG HP1 HP2 HT HD1 HD2 HDT.
 destruct(source_pair_union_conditions_total M count left right guard)as(pair&union&condition&pair'&union'&padded&
  HP&HU&HC&HP'&HU'&HAnd&HPad&BCond&BPad).
 set(rho:=conjunction_point_environment M count left right guard).
 pose proof(conjunction_point_names_bound M count left right guard)as HNames.
 pose proof(conjunction_hole_bound M count left BL)as B4.
 pose proof(conjunction_hole_bound M count right BR)as B5.
 pose proof(conjunction_hole_bound M count guard BG)as B6.
 pose proof(double_difference_all_expression_bound M rho(addM M count(code_numeral M 6))pair_union_left_template HNames B4 B5 B6 point1 HP1)as BP1.
 pose proof(double_difference_all_expression_bound M rho(addM M count(code_numeral M 6))pair_union_right_template HNames B4 B5 B6 point2 HP2)as BP2.
 pose proof(double_difference_all_expression_bound M rho(addM M count(code_numeral M 6))pair_union_conclusion HNames B4 B5 B6 target HT)as BT.
 destruct(sf_relation_total M SFImpl point2 target)as(innerPoint&HIP).
 destruct(sf_relation_total M SFImpl point1 innerPoint)as(point&HPoint).
 destruct(sf_relation_total M SFImpl padded point)as(proof&HProof).
 pose proof(source_zfr_pair_union_point_law M rho(addM M count(code_numeral M 6))pair' union' padded
  point1 point2 target innerPoint point proof HNames B4 B5 B6 HP' HU' HP1 HP2 HT HAnd HIP HPoint HProof)as PProof.
 destruct(sf_relation_total M SFImpl rep2 repTarget)as(inner&HI).
 destruct(sf_relation_total M SFImpl rep1 inner)as(body&HB).
 destruct(sf_relation_total M SFImpl condition body)as(law&HL).
 exists pair,union,condition,inner,body,law. refine(conj HP(conj HU(conj HC(conj HI(conj HB(conj HL _)))))).
 apply(proj1(source_zfr_descriptor_provable M law)).
 exact(source_descriptor_dn_padded_binary_map M ZFRSourceDescriptor count condition padded point1 point2 target rep1 rep2 repTarget
  innerPoint point proof inner body law(code_numeral M 4)BCond BP1 BP2 BT HPad HD1 HD2 HDT HIP HPoint HProof HI HB HL
  (proj2(source_zfr_descriptor_provable M proof)PProof)).
Qed.
Print Assumptions source_pair_union_conditions_total.
Print Assumptions source_zfr_canonical_pair_union_dn.
