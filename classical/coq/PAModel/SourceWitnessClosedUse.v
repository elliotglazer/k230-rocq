(** Actual witness_closed specialization. The exact matrix_request graph
    and its source proof are both constructed for arbitrary internal phi. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource
  SourceRoleReopening SourceUpperWitnessRecipes SourceWitnessMatrixSpecialization
  SourceInstantiationConstructors SourceSequents NumericalSourceFull SourceDerivedRules.
Unset Implicit Arguments.

Lemma source_upper_matrix_request_join M mat b member pair some bounded request :
  sf_relation M SFMember (zeroM M) (succM M b) member ->
  sf_relation M SFAnd member mat pair ->sf_relation M SFEx mat (zeroM M) some ->
  sf_relation M SFEx pair (zeroM M) bounded ->sf_relation M SFImpl some bounded request ->
  code_relation M (schema_env3 mat b b)
    (E_upper_matrix_request (CEvar 0) (CEvar 1)) request.
Proof.
  intros HM HP HS HB HR.
  assert (HMember:code_relation M (schema_env3 mat b b)
    (E_sf SFMember (CEconst 0) (CEadd (CEvar 1) (CEconst 1))) member).
  { exact (proj2 (schema_expression_graph M (schema_env3 mat b b) SFMember (CEconst 0)
      (CEadd (CEvar 1) (CEconst 1)) (zeroM M) (succM M b)
      member eq_refl (source_name_plus_one_graph M mat b)) HM). }
  assert (HPair:code_relation M (schema_env3 mat b b)
    (E_sf SFAnd (E_sf SFMember (CEconst 0) (CEadd (CEvar 1) (CEconst 1))) (CEvar 0)) pair).
  { exact (proj2 (schema_expression_graph M (schema_env3 mat b b) SFAnd
      (E_sf SFMember (CEconst 0) (CEadd (CEvar 1) (CEconst 1))) (CEvar 0) member mat pair HMember eq_refl) HP). }
  assert (HSome:code_relation M (schema_env3 mat b b) (E_sf_ex (CEvar 0)) some).
  { exact (proj2 (schema_expression_graph M (schema_env3 mat b b) SFEx (CEvar 0) (CEconst 0) mat (zeroM M) some eq_refl eq_refl) HS). }
  assert (HBound:code_relation M (schema_env3 mat b b)
    (E_sf_ex (E_sf SFAnd (E_sf SFMember (CEconst 0) (CEadd (CEvar 1) (CEconst 1))) (CEvar 0))) bounded).
  { exact (proj2 (schema_expression_graph M (schema_env3 mat b b) SFEx
      (E_sf SFAnd (E_sf SFMember (CEconst 0) (CEadd (CEvar 1) (CEconst 1))) (CEvar 0))
      (CEconst 0) pair (zeroM M) bounded HPair eq_refl) HB). }
  exact (proj2 (schema_expression_graph M (schema_env3 mat b b) SFImpl
    (E_sf_ex (CEvar 0))
    (E_sf_ex (E_sf SFAnd (E_sf SFMember (CEconst 0) (CEadd (CEvar 1) (CEconst 1))) (CEvar 0)))
    some bounded request HSome HBound) HR).
Qed.

Theorem source_full_upper_witness_closed_use_total M cb cc cn phi k delta b closed p pb :
  source_bounded M phi k ->source_upper_witness_closed_recipe M phi delta b closed ->
  sf_relation M SFMember p b pb ->source_full_prv M cb cc cn closed ->
  source_full_prv M cb cc cn pb ->
  exists request,source_upper_matrix_request_recipe M phi delta p b request /\
    source_full_prv M cb cc cn request.
Proof.
  intros HP [mat [HMat HClosed]] HPb PClosed PPb.
  destruct (source_upper_witness_closed_shell M mat b closed HClosed)
    as (guard & member & pair & some & bounded & request & point & HGuard & HMember & HPair &
      HSome & HBound & HRequest & HPoint & HAll).
  destruct (numerical_instantiation_total M point p)
    as [point' [ib [ic [HInput HPointSub]]]].
  destruct (proj1 (numerical_substitution_binary M SFImpl guard request point ib ic
    (code_numeral M 1) (zeroM M) point' (or_intror (or_intror eq_refl)) HPoint) HPointSub)
    as [guard' [request' [HGuardSub [HRequestSub HPoint']]]].
  destruct (proj1 (numerical_substitution_member M (zeroM M) (succM M b) guard ib ic
    (code_numeral M 1) (zeroM M) guard' HGuard) HGuardSub)
    as [a [d [HA [HD HGuard']]]].
  pose proof (substitution_lookup_functional M ib ic (code_numeral M 1) (zeroM M)
    (zeroM M) a p HA HInput) as E. subst a.
  pose proof (substitution_lookup_functional M ib ic (code_numeral M 1) (zeroM M)
    (succM M b) d b HD (substitution_singleton_tail M ib ic b)) as E. subst d.
  pose proof (sf_relation_functional M SFMember p b guard' pb HGuard' HPb) as E. subst guard'. clear HA HD HGuard'.
  destruct (proj1 (numerical_substitution_binary M SFImpl some bounded request ib ic
    (code_numeral M 1) (zeroM M) request' (or_intror (or_intror eq_refl)) HRequest) HRequestSub)
    as [some' [bounded' [HSomeSub [HBoundSub HRequest']]]].
  destruct (proj1 (numerical_substitution_quantifier M false mat some ib ic
    (code_numeral M 1) (zeroM M) some' HSome) HSomeSub)
    as [ad [ae [am [mat' [HL1 [HMat' HSome']]]]]].
  destruct (proj1 (numerical_substitution_quantifier M false pair bounded ib ic
    (code_numeral M 1) (zeroM M) bounded' HBound) HBoundSub)
    as [dd [de [dm [pair' [HL2 [HPairSub HBound']]]]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd member mat pair dd de dm
    (code_numeral M 1) pair' (or_introl eq_refl) HPair) HPairSub)
    as [member' [mat'' [HMemberSub [HMat'' HPair']]]].
  pose proof (numerical_substitution_functional_equivalent M mat ad ae am dd de dm
    (code_numeral M 1) mat' mat'' (substitution_lift_functional M ib ic
      (code_numeral M 1) (zeroM M) ad ae am dd de dm HL1 HL2) HMat' HMat'') as E.
  subst mat''.
  destruct (proj1 (numerical_substitution_member M (zeroM M) (succM M (succM M b))
    member dd de dm (code_numeral M 1) member' HMember) HMemberSub)
    as [a [d [HA [HD HMember']]]].
  apply (proj1 (substitution_lift_head M ib ic (code_numeral M 1) (zeroM M) dd de dm a HL2)) in HA.
  subst a.
  assert (HAct:substitution_lookup M dd de dm (code_numeral M 1)
    (succM M (succM M b)) (succM M b)).
  { apply (proj2 (substitution_lift_tail M ib ic (code_numeral M 1) (zeroM M)
      dd de dm (succM M b) b HL2)). apply substitution_singleton_tail. }
  pose proof (substitution_lookup_functional M dd de dm (code_numeral M 1)
    (succM M (succM M b)) d (succM M b) HD HAct) as E. subst d.
  destruct (source_role_reopening_total M (succM M p) (zeroM M)) as [rb [rc HMap]].
  pose proof (source_witness_matrix_specialization M phi mat p k delta ib ic ad ae am rb rc mat'
    HP HMat HInput HL1 HMat' HMap) as HMatrix.
  exists request'. split.
  - exists rb,rc,mat'. split;[exact HMap|]. split;[exact HMatrix|].
    exact (source_upper_matrix_request_join M mat' b member' pair' some' bounded' request'
      HMember' HPair' HSome' HBound' HRequest').
  - apply (source_full_modus_ponens M cb cc cn pb request' point' HPoint');[|exact PPb].
    apply (full_source_AllE M cb cc cn point closed p point').
    + apply (source_wf_quantifier_instance M cb cc cn SFAll point closed p point'
        (or_introl eq_refl) HAll (source_full_prv_wellformed M cb cc cn closed PClosed)).
      now exists ib,ic.
    + exact PClosed.
    + exact HAll.
    + now exists ib,ic.
Qed.

Print Assumptions source_upper_matrix_request_join.
Print Assumptions source_full_upper_witness_closed_use_total.
