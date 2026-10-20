(** Literal finite profile substitution, for calibrating the fixed lookup
    law at arbitrary model-valued variable names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceAtomLookupOld SourceEnvFLookupProfile SourceFiniteParameters SourceFiniteParameterComposition SourceFiniteNameParameters
 SourceParameterGraphs SourceParameterIdentityCalibration.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF.
From OldZFC Require Z_base.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Lemma old_env_profile_subst e i a sg:
 (@OC.subst_form OB.sig_empty OldUndecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on sg(old_atom_app_profile e i a))=
 old_atom_app_profile(OC.subst_term sg e)(OC.subst_term sg i)(OC.subst_term sg a).
Proof.
 unfold old_atom_app_profile. cbn[OC.subst_form]. rewrite OldZFC.Z_base.App0_subst.
 cbn[Vector.map OC.subst_term OC.up]. rewrite!OldUndecidability.FOL.Syntax.Subst.up_term. reflexivity.
Qed.
Lemma isolated_env_profile_at e i a:
 isolated_formula(old_atom_app_profile e i a)=
 C.subst_form(C.scons(isolated_term e)(C.scons(isolated_term i)(C.scons(isolated_term a)C.var)))source_env_profile_predicate.
Proof.
 pose proof(isolated_formula_subst(old_atom_app_profile(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))
  (OC.scons e(OC.scons i(OC.scons a OC.var)))
  (C.scons(isolated_term e)(C.scons(isolated_term i)(C.scons(isolated_term a)C.var)))ltac:(intros[|[|[|j]]];reflexivity))as HE.
 rewrite old_env_profile_subst in HE. exact HE.
Qed.
Theorem source_parameter_env_profile_instance M names rho e i a ev iv av out:
 code_relation M rho(names e)ev->code_relation M rho(names i)iv->code_relation M rho(names a)av->
 code_relation M rho(source_parameter_expression names(isolated_formula(old_atom_app_profile(@OC.var OB.sig_empty e)(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty a))))out->
 source_env_profile M ev iv av out.
Proof.
 intros HE HI HA HG. rewrite isolated_env_profile_at,source_parameter_substitution in HG.
 set(sg:=C.scons(C.var e)(C.scons(C.var i)(C.scons(C.var a)C.var))).
 assert(HNames:forall k v,(k<3)%nat->
  (code_relation M rho(names(sf_index(sg k)))v<->code_relation M(source_env_profile_environment ev iv av)(source_finite_parameter_names 3 k)v)).
 { intros[|[|[|k]]] v HK;try lia.
   - change(code_relation M rho(names e)v<->v=ev). split;[intro HV;exact(code_relation_functional M(names e)rho v ev HV HE)|intros->;exact HE].
   - change(code_relation M rho(names i)v<->v=iv). split;[intro HV;exact(code_relation_functional M(names i)rho v iv HV HI)|intros->;exact HI].
   - change(code_relation M rho(names a)v<->v=av). split;[intro HV;exact(code_relation_functional M(names a)rho v av HV HA)|intros->;exact HA]. }
 exact(proj1(source_parameter_graph_ext M 3 source_env_profile_predicate source_env_profile_finite_bound
  (fun k=>names(sf_index(sg k)))(source_finite_parameter_names 3)rho(source_env_profile_environment ev iv av)HNames out)HG).
Qed.
Theorem source_env_profile_old_numeral M e i a:
 source_env_profile M(code_numeral M e)(code_numeral M i)(code_numeral M a)
  (code_numeral M(sf_encode(isolated_formula(old_atom_app_profile(@OC.var OB.sig_empty e)(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty a))))).
Proof.
 apply(source_parameter_env_profile_instance M(fun j=>CEconst j)(fun _=>zeroM M)e i a(code_numeral M e)(code_numeral M i)(code_numeral M a));try reflexivity.
 apply source_parameter_identity_calibration. intros j. reflexivity.
Qed.
Print Assumptions source_parameter_env_profile_instance.
Print Assumptions source_env_profile_old_numeral.



