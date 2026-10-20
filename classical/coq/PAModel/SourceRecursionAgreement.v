(** Literal agreement shell and actual two-universal agreement elimination. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters
 SourceParameterGraphs SourceParameterTransport SourcePropositionalRebase SourceRecursionParameterCalibration
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceDoubleSpecialization SourceRoleReopening
 SourceFiniteCutoffShift SourceTripleSpecialization NumericalSubstitutionMaps NumericalSubstitution
 NumericalContexts NumericalSourceFull SourceTraceBounds SourceDerivedRules SetSchemaConstructors SchemaConstructorBounds.
From OldZF Require Std_setbase Std_setrec.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_rec_agreement_bounded M f g z out k:
 coding_lt M f k ->coding_lt M g k ->coding_lt M z k ->source_rec_agreement M f g z out ->source_bounded M out k.
Proof.
 intros HF HG HZ HO. apply(source_parameter_graph_bounded M 3 source_rec_agreement_predicate source_rec_agreement_finite_bound
  (source_finite_parameter_names 3)(source_rec_env3 f g z)k);[|exact HO].
 intros[|[|[|i]]]x HI HX;try lia.
 - change(x=f)in HX. now subst x.
 - change(x=g)in HX. now subst x.
 - change(x=z)in HX. now subst x.
Qed.
Theorem source_rec_agreement_substitution M f g z out f' g' z' out' rb rc rn base:
 source_rec_agreement M f g z out ->source_rec_agreement M f' g' z' out' ->
 substitution_lookup M rb rc rn base f f' ->substitution_lookup M rb rc rn base g g' ->
 substitution_lookup M rb rc rn base z z' ->numerical_substitution M out rb rc rn base out'.
Proof.
 intros HO HO' HF HG HZ.
 apply(source_parameter_transport M 3 source_rec_agreement_predicate source_rec_agreement_finite_bound
  (source_finite_parameter_names 3)(source_finite_parameter_names 3)(source_rec_env3 f g z)(source_rec_env3 f' g' z')
  rb rc rn base out out');[|exact HO|exact HO'].
 intros[|[|[|i]]]x y HI HX HY;try lia.
 - change(x=f)in HX. change(y=f')in HY. now subst x y.
 - change(x=g)in HX. change(y=g')in HY. now subst x y.
 - change(x=z)in HX. change(y=z')in HY. now subst x y.
Qed.

Theorem source_rec_agreement_shell M f g z out:
 source_rec_agreement M f g z out ->exists left right equal rhs point inner,
 source_rec_app M(succM M(succM M f))(succM M(succM M z))(code_numeral M 1)left /\
 source_rec_app M(succM M(succM M g))(succM M(succM M z))(zeroM M)right /\
 sf_relation M SFEqual(code_numeral M 1)(zeroM M)equal /\sf_relation M SFImpl right equal rhs /\
 sf_relation M SFImpl left rhs point /\sf_relation M SFAll point(zeroM M)inner /\sf_relation M SFAll inner(zeroM M)out.
Proof.
 intro HO. set(rho:=source_rec_env3 f g z).
 set(names:=source_parameter_up(source_parameter_up(source_finite_parameter_names 3))).
 change(code_relation M rho(E_sf SFAll(E_sf SFAll(E_sf SFImpl
  (source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 1))))
  (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 0))))
   (E_sf SFEqual(CEadd(CEconst 0)(CEconst 1))(CEconst 0))))(CEconst 0))(CEconst 0))out)in HO.
 destruct(schema_expression_split M rho SFAll _ _ out HO)as(inner&z0&HInner&HZ0&HOuter).
 change(z0=zeroM M)in HZ0. subst z0.
 destruct(schema_expression_split M rho SFAll _ _ inner HInner)as(point&z0&HPoint&HZ0&HAll).
 change(z0=zeroM M)in HZ0. subst z0.
 destruct(schema_expression_split M rho SFImpl _ _ point HPoint)as(left&rhs&HLeft&HRhs&HImp).
 destruct(schema_expression_split M rho SFImpl _ _ rhs HRhs)as(right&equal&HRight&HEqual&HRightImp).
 assert(N0:code_relation M rho(names 0)(zeroM M))by reflexivity.
 assert(N1:code_relation M rho(names 1)(code_numeral M 1)).
 { exact(source_parameter_up_name M(source_parameter_up(source_finite_parameter_names 3))rho 0(zeroM M)eq_refl). }
 assert(N2:code_relation M rho(names 2)(succM M(succM M f))).
 { apply(source_parameter_up_name M _ rho 1(succM M f)). apply(source_parameter_up_name M _ rho 0 f). reflexivity. }
 assert(N3:code_relation M rho(names 3)(succM M(succM M g))).
 { apply(source_parameter_up_name M _ rho 2(succM M g)). apply(source_parameter_up_name M _ rho 1 g). reflexivity. }
 assert(N4:code_relation M rho(names 4)(succM M(succM M z))).
 { apply(source_parameter_up_name M _ rho 3(succM M z)). apply(source_parameter_up_name M _ rho 2 z). reflexivity. }
 exists left,right,equal,rhs,point,inner.
 split;[exact(source_parameter_rec_app M names rho 2 4 1 _ _ _ left N2 N4 N1 HLeft)|].
 split;[exact(source_parameter_rec_app M names rho 3 4 0 _ _ _ right N3 N4 N0 HRight)|].
 split;[|repeat split;assumption].
 exact(proj1(schema_expression_graph M rho SFEqual _ _ (code_numeral M 1)(zeroM M)equal N1 N0)HEqual).
Qed.

Theorem source_full_rec_agreement_use M cb cc cn f g z agreement v w left right equal:
 source_rec_agreement M f g z agreement ->source_rec_app M f z v left ->source_rec_app M g z w right ->
 sf_relation M SFEqual v w equal ->source_full_prv M cb cc cn agreement ->
 source_full_prv M cb cc cn left ->source_full_prv M cb cc cn right ->source_full_prv M cb cc cn equal.
Proof.
 intros HA HL HR HE PA PL PR.
 destruct(source_rec_agreement_shell M f g z agreement HA)as(l&r&e&rhs&point&inner&HLeft&HRight&HEqual&HRightImp&HPoint&HAll&HOuter).
 destruct(source_role_reopening_total M v w)as(tb&tc&HT).
 pose proof(source_rec_app_substitution M(succM M(succM M f))(succM M(succM M z))(code_numeral M 1)l
  f z v left tb tc(code_numeral M 2)(zeroM M)HLeft HL(source_role_reopening_tail M tb tc f)
  (source_role_reopening_tail M tb tc z)(proj2 HT))as HSL.
 pose proof(source_rec_app_substitution M(succM M(succM M g))(succM M(succM M z))(zeroM M)r
  g z w right tb tc(code_numeral M 2)(zeroM M)HRight HR(source_role_reopening_tail M tb tc g)
  (source_role_reopening_tail M tb tc z)(proj1 HT))as HSR.
 assert(HSE:numerical_substitution M e tb tc(code_numeral M 2)(zeroM M)equal).
 { apply(proj2(numerical_substitution_equal M _ _ e tb tc(code_numeral M 2)(zeroM M)equal HEqual)).
   exists v,w. exact(conj(proj2 HT)(conj(proj1 HT)HE)). }
 destruct(sf_relation_total M SFImpl right equal)as(targetR&HTR).
 destruct(sf_relation_total M SFImpl left targetR)as(target&HTarget).
 assert(SubR:numerical_substitution M rhs tb tc(code_numeral M 2)(zeroM M)targetR).
 { apply(proj2(numerical_substitution_binary M SFImpl r e rhs tb tc(code_numeral M 2)(zeroM M)targetR(or_intror(or_intror eq_refl))HRightImp)).
   exists right,equal. auto. }
 assert(Sub:numerical_substitution M point tb tc(code_numeral M 2)(zeroM M)target).
 { apply(proj2(numerical_substitution_binary M SFImpl l rhs point tb tc(code_numeral M 2)(zeroM M)target(or_intror(or_intror eq_refl))HPoint)).
   exists left,targetR. auto. }
 destruct(source_full_prv_wellformed M cb cc cn agreement PA)as(k&BA&BC).
 pose proof(proj1(source_bounded_accept_unary M SFAll inner agreement k(or_introl eq_refl)HOuter)BA)as BI.
 pose proof(proj1(source_bounded_accept_unary M SFAll point inner(succM M k)(or_introl eq_refl)HAll)BI)as BP.
 pose proof(source_full_double_specialize M cb cc cn point inner agreement v w tb tc target(succM M(succM M k))BP HAll HOuter HT Sub PA)as PT.
 exact(source_full_modus_ponens M cb cc cn right equal targetR HTR
  (source_full_modus_ponens M cb cc cn left targetR target HTarget PT PL)PR).
Qed.
Print Assumptions source_rec_agreement_bounded.
Print Assumptions source_rec_agreement_substitution.
Print Assumptions source_rec_agreement_shell.
Print Assumptions source_full_rec_agreement_use.
