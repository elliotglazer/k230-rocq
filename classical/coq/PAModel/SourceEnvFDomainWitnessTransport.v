(** Actual source substitution and literal finite calibration for Dom0. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceEnvFDomainGraph SourceBounded
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteParameterComposition SourceFiniteNameParameters
 SourceParameterGraphs SourceParameterTransport SourceParameterIdentityCalibration
 NumericalSubstitutionMaps NumericalSubstitution SourceFiniteCutoffShift.
From OldZFC Require Z_base.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_env_domain_substitution M e d out e' d' out' b c n base:
 source_env_domain M e d out->source_env_domain M e' d' out'->
 substitution_lookup M b c n base e e'->substitution_lookup M b c n base d d'->
 numerical_substitution M out b c n base out'.
Proof.
 intros HO HO' HE HD. apply(source_parameter_transport M 2 source_env_domain_predicate source_env_domain_finite_bound
  (source_finite_parameter_names 2)(source_finite_parameter_names 2)(sf_env e d)(sf_env e' d')b c n base out out');[|exact HO|exact HO'].
 intros[|[|i]] x y HI HX HY;try lia.
 - change(x=e)in HX. change(y=e')in HY. now subst x y.
 - change(x=d)in HX. change(y=d')in HY. now subst x y.
Qed.
Theorem source_env_domain_cutoff_two M dom:source_env_domain M(code_numeral M 1)(zeroM M)dom->source_cutoff_shift M 2 dom dom.
Proof.
 intro HD. destruct(source_cutoff_shift_map_total M 2)as(b&c&n&HM).
 exists b,c,n. split;[exact HM|].
 exact(source_env_domain_substitution M(code_numeral M 1)(zeroM M)dom(code_numeral M 1)(zeroM M)dom b c n(code_numeral M 3)
  HD HD(source_cutoff_shift_map_fixed_lookup M 2 b c n HM 1)(source_cutoff_shift_map_fixed_lookup M 2 b c n HM 0)).
Qed.
Lemma isolated_Dom_at e d:
 isolated_formula(OldZFC.Z_base.Dom0 e d)=
 C.subst_form(C.scons(isolated_term e)(C.scons(isolated_term d)C.var))source_env_domain_predicate.
Proof.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))
  (OC.scons e(OC.scons d OC.var))(C.scons(isolated_term e)(C.scons(isolated_term d)C.var))ltac:(intros[|[|i]];reflexivity))as HE.
 rewrite OldZFC.Z_base.Dom0_subst in HE. exact HE.
Qed.
Theorem source_parameter_Dom_instance M names rho i j e d out:
 code_relation M rho(names i)e->code_relation M rho(names j)d->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j))))out->
 source_env_domain M e d out.
Proof.
 intros HE HD HG. rewrite isolated_Dom_at,source_parameter_substitution in HG.
 assert(HNames:forall k v,(k<2)%nat->
  (code_relation M rho(names(sf_index((C.scons(C.var i)(C.scons(C.var j)C.var))k)))v<->
   code_relation M(sf_env e d)(source_finite_parameter_names 2 k)v)).
 { intros[|[|k]] v HK;try lia.
   - change(code_relation M rho(names i)v<->v=e). split;[intro HV;exact(code_relation_functional M(names i)rho v e HV HE)|intros->;exact HE].
   - change(code_relation M rho(names j)v<->v=d). split;[intro HV;exact(code_relation_functional M(names j)rho v d HV HD)|intros->;exact HD]. }
 exact(proj1(source_parameter_graph_ext M 2 source_env_domain_predicate source_env_domain_finite_bound
  (fun k=>names(sf_index((C.scons(C.var i)(C.scons(C.var j)C.var))k)))(source_finite_parameter_names 2)rho(sf_env e d)HNames out)HG).
Qed.
Theorem source_env_domain_old_numeral M e d:
 source_env_domain M(code_numeral M e)(code_numeral M d)
  (code_numeral M(sf_encode(isolated_formula(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty e)(@OC.var OB.sig_empty d))))).
Proof.
 apply(source_parameter_Dom_instance M(fun i=>CEconst i)(fun _=>zeroM M)e d(code_numeral M e)(code_numeral M d));try reflexivity.
 apply source_parameter_identity_calibration. intros i. reflexivity.
Qed.
Print Assumptions source_env_domain_substitution.
Print Assumptions source_env_domain_cutoff_two.
Print Assumptions source_parameter_Dom_instance.
Print Assumptions source_env_domain_old_numeral.
