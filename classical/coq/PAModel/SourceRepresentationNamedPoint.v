(** Exact representative-name normalization of the quantified point in
    the uniform representation statement. All matrix holes are internal codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions CodeExpressionPlug
 SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceNumeralLift NumericalRenamingMaps NumericalRenaming
 SourceRepresentationRecipe SourceRepresentativeRenaming SourceRepresentationRepresentativePoint
 SourceSetRelativization SourceSetRelativizationFunctionality SourceSetRelativizationRenaming
 SourcePropositionalTemplates SourcePropositionalRenaming SourceDefinabilityBounds SourceFiniteCutoffShift.
Unset Implicit Arguments.
Definition E_representation_named_inner :=E_sf SFImpl(CEvar 0)
 (E_sf_iff(E_sf SFMember(CEconst 0)(CEvar 2))(CEvar 1)).
Definition E_representation_named_point :=E_sf SFAll E_representation_named_inner(CEconst 0).
Definition representation_inner_pattern :=SPTImpl(SPTSlot 0)
 (SPTAnd(SPTImpl(SPTSlot 1)(SPTSlot 2))(SPTImpl(SPTSlot 2)(SPTSlot 1))).
Definition representation_inner_plug i :=match i with 0=>CEvar 0|1=>E_sf SFMember(CEconst 0)(CEvar 2)|_=>CEvar 1 end.
Lemma representation_inner_graph M environment matrix name atom inner :
 sf_relation M SFMember(zeroM M) name atom ->
 (code_relation M(schema_env3 environment matrix name) E_representation_named_inner inner <->
 code_relation M(schema_env3 environment atom matrix)(source_prop_expression representation_inner_pattern) inner).
Proof.
 intro HA. change(code_relation M(schema_env3 environment matrix name)
   (code_plug representation_inner_plug(source_prop_expression representation_inner_pattern)) inner <->code_relation M(schema_env3 environment atom matrix)(source_prop_expression representation_inner_pattern) inner).
 apply code_relation_plug. intros[|[|i]];cbn[representation_inner_plug schema_env3];try reflexivity.
 exact(proj2(schema_expression_graph M(schema_env3 environment matrix name) SFMember
  (CEconst 0)(CEvar 2)(zeroM M) name atom eq_refl eq_refl) HA).
Qed.

Theorem source_representative_lift_fixes_relative_matrix M phi matrix relative k r b c n :
 source_bounded M phi k ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) matrix ->
 source_set_relativization M(code_numeral M 2) matrix relative ->
 renaming_lift M r r(code_numeral M 1)(zeroM M) b c n ->
 numerical_renaming M relative b c n(zeroM M) relative.
Proof.
 intros HP HM HR HL.
 assert(HCarrier:renaming_lookup M b c n(zeroM M)(code_numeral M 2)(code_numeral M 2)).
 { apply(representative_lift_fixed M r b c n _ HL). intro E.
   apply(Model.succ_injective M)in E. exact(Model.zero_ne_succ M(zeroM M)(eq_sym E)). }
 destruct(source_set_relativization_renaming_exists M matrix(code_numeral M 2)(code_numeral M 2)
   b c n(zeroM M) matrix relative HCarrier
   (source_representative_lift_fixes_shift_three M phi matrix k r b c n HP HM HL) HR)
   as(other&HOther&HMap).
 assert(E:other=relative)by(eapply source_set_relativization_functional;eassumption).
 now subst other.
Qed.

Theorem source_representation_point_renaming M environment matrix body renamed r b c n :
 renaming_lift M r r(code_numeral M 1)(zeroM M) b c n ->
 numerical_renaming M environment b c n(zeroM M) environment ->
 numerical_renaming M matrix b c n(zeroM M) matrix ->
 code_relation M(schema_env3 environment matrix(code_numeral M 1)) E_representation_named_point body ->
 code_relation M(schema_env3 environment matrix(succM M r)) E_representation_named_point renamed ->
 source_representative_renaming M r body renamed.
Proof.
 intros HL HE HM HBody HRenamed.
 destruct(code_relation_total M E_representation_named_inner(schema_env3 environment matrix(code_numeral M 1)))as(inner&HInner).
 destruct(code_relation_total M E_representation_named_inner(schema_env3 environment matrix(succM M r)))as(inner'&HInner').
 pose proof(proj1(schema_expression_graph M _ SFAll E_representation_named_inner(CEconst 0)
   inner(zeroM M) body HInner eq_refl) HBody)as HAll.
 pose proof(proj1(schema_expression_graph M _ SFAll E_representation_named_inner(CEconst 0)
   inner'(zeroM M) renamed HInner' eq_refl) HRenamed)as HAll'.
 destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 1))as(atom&HAtom).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M r))as(atom'&HAtom').
 assert(HAtomMap:numerical_renaming M atom b c n(zeroM M) atom').
 { apply(proj2(numerical_renaming_member M _ _ atom b c n(zeroM M) atom' HAtom)).
   exists(zeroM M),(succM M r). split.
   - exact(proj2(renaming_lift_head M r r(code_numeral M 1)(zeroM M) b c n(zeroM M) HL) eq_refl).
   - exact(conj(representative_lift_one M r b c n HL) HAtom'). }
 assert(HInnerMap:numerical_renaming M inner b c n(zeroM M) inner').
 { apply(source_prop_expression_renaming M(schema_env3 environment atom matrix)
    (schema_env3 environment atom' matrix)b c n(zeroM M) representation_inner_pattern inner inner').
   - intros[|[|i]];cbn[schema_env3];assumption.
   - exact(proj1(representation_inner_graph M environment matrix(code_numeral M 1) atom inner HAtom) HInner).
   - exact(proj1(representation_inner_graph M environment matrix(succM M r) atom' inner' HAtom') HInner'). }
 apply(proj2(numerical_renaming_quantifier M true inner body r r(code_numeral M 1)(zeroM M) renamed HAll)).
 exists b,c,n,inner'. exact(conj HL(conj HInnerMap HAll')).
Qed.
Print Assumptions source_representative_lift_fixes_relative_matrix.
Print Assumptions source_representation_point_renaming.


