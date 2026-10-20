(** The canonical representation recipe can be reopened at any free set
    name r>=2. The Dn assignment variables remain bound; r is never captured. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions CodeExpressionPlug
 SetFormulaCodes SetSchemaConstructors SourceBounded SourceBoundMonotone SchemaConstructorBounds
 SourceDefinabilityBounds SourceFiniteCutoffShift SourceRenamingBounds SourceSetRelativization SourceSetRelativizationBounds
 SourceRepresentationRecipe SourceRepresentationNamedPoint SourceRepresentationRepresentativePoint
 SourceRepresentativeRenaming SourceDnRepresentativeTransport SourceDn
 NumericalRenamingMaps NumericalRenaming.
Unset Implicit Arguments.

Lemma representation_standard_point_graph M environment matrix body :
 code_relation M(representation_point_environment environment matrix)
   (E_representation_point(CEvar 0)(CEvar 1)) body <->
 code_relation M(schema_env3 environment matrix(code_numeral M 1)) E_representation_named_point body.
Proof.
 change(code_relation M(representation_point_environment environment matrix)
   (code_plug(fun i=>match i with 0=>CEvar 0|1=>CEvar 1|_=>CEconst 1 end)
     E_representation_named_point)body <->code_relation M(schema_env3 environment matrix(code_numeral M 1)) E_representation_named_point body).
 apply code_relation_plug. intros[|[|i]];reflexivity.
Qed.

Lemma source_representation_point_bound M n phi environment first shifted matrix relative body :
 source_bounded M phi n ->source_envf M n environment ->
 source_cutoff_shift M 1 environment first ->source_cutoff_shift M 1 first shifted ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) matrix ->
 source_set_relativization M(code_numeral M 2) matrix relative ->
 code_relation M(representation_point_environment shifted relative)
  (E_representation_point(CEvar 0)(CEvar 1)) body ->
 source_bounded M body(succM M(succM M n)).
Proof.
 intros HP HE H1 H2 HM HR HB.
 pose proof(source_cutoff_shift_bounded M 1 environment first n(source_envf_bound M n environment HE) H1)as BA.
 pose proof(source_cutoff_shift_bounded M 1 first shifted(succM M n) BA H2)as BB.
 assert(BM:source_bounded M matrix(succM M(succM M(succM M n)))).
 { apply(numerical_renaming_preserves_bound M phi _ _ _ _ matrix n _ HP HM).
   intros i j HI HJ. apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)
     (code_numeral M 3) i j(coding_not_lt_zero M i))in HJ. subst j.
   rewrite Arithmetic.add_comm. change(coding_lt M(addM M(succM M(succM M(succM M(zeroM M)))) i)
     (succM M(succM M(succM M n)))). rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
   do 3 apply coding_lt_succ_cancel. exact HI. }
 assert(BR:source_bounded M relative(succM M(succM M(succM M n)))).
 { apply(source_set_relativization_preserves_bound M matrix(code_numeral M 2) _ relative);try assumption.
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(B:schema_expression_bound M(representation_point_environment shifted relative)
   (E_representation_point(CEvar 0)(CEvar 1))(succM M(succM M n))).
 { unfold E_representation_point,E_sf_iff. repeat schema_constructor_bound;try schema_small_index;assumption. }
 exact(B body HB).
Qed.

Theorem source_representation_named_recipe M n phi result r renamed :
 source_bounded M phi n ->source_representation_recipe M n phi result ->
 ~coding_lt M r(code_numeral M 2) ->source_representative_renaming M r result renamed ->
 exists environment first shifted matrix relative body,
 source_envf M n environment /\source_cutoff_shift M 1 environment first /\
 source_cutoff_shift M 1 first shifted /\
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) matrix /\
 source_set_relativization M(code_numeral M 2) matrix relative /\
 code_relation M(schema_env3 shifted relative(succM M(addM M r n))) E_representation_named_point body /\
 source_dn M n body renamed.
Proof.
 intros HP(environment&first&shifted&matrix&relative&original&HE&H1&H2&HM&HR&HOriginal&HD) HRBound HResult.
 destruct(code_relation_total M E_representation_named_point
   (schema_env3 shifted relative(succM M(addM M r n))))as(body&HBody).
 destruct(renaming_lift_total M(addM M r n)(addM M r n)(code_numeral M 1)(zeroM M))as(b&c&l&HL).
 assert(HOriginalMap:source_representative_renaming M(addM M r n) original body).
 { apply(source_representation_point_renaming M shifted relative original body(addM M r n)b c l HL).
   - apply(source_representative_lift_fixes_cutoff_one M first shifted(succM M(succM M n))(addM M r n)b c l).
     + exact(source_cutoff_shift_bounded M 1 environment first n(source_envf_bound M n environment HE) H1).
     + exact H2.
     + exact HL.
   - exact(source_representative_lift_fixes_relative_matrix M phi matrix relative n(addM M r n)b c l HP HM HR HL).
   - exact(proj1(representation_standard_point_graph M shifted relative original) HOriginal).
   - exact HBody. }
 exists environment,first,shifted,matrix,relative,body.
 refine(conj HE(conj H1(conj H2(conj HM(conj HR(conj HBody _)))))).
 apply(source_dn_representative_transport M n original result body renamed r(zeroM M));try assumption.
 pose proof(source_representation_point_bound M n phi environment first shifted matrix relative original
   HP HE H1 H2 HM HR HOriginal)as B.
 change(source_bounded M original(addM M n(code_numeral M 2))).
 rewrite Arithmetic.add_comm. change(source_bounded M original(addM M(succM M(succM M(zeroM M))) n)).
 now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Print Assumptions representation_standard_point_graph.
Print Assumptions source_representation_point_bound.
Print Assumptions source_representation_named_recipe.


