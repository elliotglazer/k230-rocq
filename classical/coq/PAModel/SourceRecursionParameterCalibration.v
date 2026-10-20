(** Literal parameter-compilation bridges for App and Agr inside fixed laws. *)
From PAModel Require Import Model Arithmetic CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteParameterComposition SourceFiniteNameParameters SourceParameterGraphs SourceRecursionPrimitiveRelations.
From OldZF Require Std_setbase Std_setrec.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_parameter_up_name M names rho i x:
 code_relation M rho(names i)x ->code_relation M rho(source_parameter_up names(S i))(succM M x).
Proof.
 intro HX. cbn[source_parameter_up code_relation]. exists x,(code_numeral M 1).
 repeat split;try assumption;try reflexivity. apply Arithmetic.succ_as_add.
Qed.

Lemma isolated_rec_app_at t u v:
 isolated_formula(OldZF.Std_setbase.App t u v)=C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))source_rec_app_predicate.
Proof.
 pose proof(isolated_formula_subst(OldZF.Std_setbase.App(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))
  (OC.scons t(OC.scons u(OC.scons v OC.var)))(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))
  ltac:(intros[|[|[|i]]];reflexivity))as HE.
 rewrite OldZF.Std_setbase.App_subst in HE. exact HE.
Qed.
Theorem source_parameter_rec_app M names rho i j k f u v out:
 code_relation M rho(names i)f ->code_relation M rho(names j)u ->code_relation M rho(names k)v ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j)(@OC.var OB.sig_empty k))))out ->
 source_rec_app M f u v out.
Proof.
 intros HF HU HV HG. rewrite isolated_rec_app_at,source_parameter_substitution in HG.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))(C.scons(isolated_term(@OC.var OB.sig_empty k))C.var))).
 assert(HNames:forall n x,(n<3)%nat ->(code_relation M rho(names(sf_index(sigma n)))x <->
  code_relation M(source_rec_env3 f u v)(source_finite_parameter_names 3 n)x)).
 { intros[|[|[|n]]]x HN;try lia.
   - change(code_relation M rho(names i)x <->x=f). split;[intro HX;exact(code_relation_functional M _ rho x f HX HF)|intros ->;exact HF].
   - change(code_relation M rho(names j)x <->x=u). split;[intro HX;exact(code_relation_functional M _ rho x u HX HU)|intros ->;exact HU].
   - change(code_relation M rho(names k)x <->x=v). split;[intro HX;exact(code_relation_functional M _ rho x v HX HV)|intros ->;exact HV]. }
 exact(proj1(source_parameter_graph_ext M 3 source_rec_app_predicate source_rec_app_finite_bound(fun n=>names(sf_index(sigma n)))
  (source_finite_parameter_names 3)rho(source_rec_env3 f u v)HNames out)HG).
Qed.
Print Assumptions source_parameter_rec_app.

Lemma isolated_rec_agreement_at t u v:
 isolated_formula(OldZF.Std_setrec.Agr t u v)=C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))source_rec_agreement_predicate.
Proof.
 pose proof(isolated_formula_subst(OldZF.Std_setrec.Agr(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))
  (OC.scons t(OC.scons u(OC.scons v OC.var)))(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))
  ltac:(intros[|[|[|i]]];reflexivity))as HE.
 rewrite OldZF.Std_setrec.Agr_subst in HE. exact HE.
Qed.
Theorem source_parameter_rec_agreement M names rho i j k f u v out:
 code_relation M rho(names i)f ->code_relation M rho(names j)u ->code_relation M rho(names k)v ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setrec.Agr(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j)(@OC.var OB.sig_empty k))))out ->
 source_rec_agreement M f u v out.
Proof.
 intros HF HU HV HG. rewrite isolated_rec_agreement_at,source_parameter_substitution in HG.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))(C.scons(isolated_term(@OC.var OB.sig_empty k))C.var))).
 assert(HNames:forall n x,(n<3)%nat ->(code_relation M rho(names(sf_index(sigma n)))x <->
  code_relation M(source_rec_env3 f u v)(source_finite_parameter_names 3 n)x)).
 { intros[|[|[|n]]]x HN;try lia.
   - change(code_relation M rho(names i)x <->x=f). split;[intro HX;exact(code_relation_functional M _ rho x f HX HF)|intros ->;exact HF].
   - change(code_relation M rho(names j)x <->x=u). split;[intro HX;exact(code_relation_functional M _ rho x u HX HU)|intros ->;exact HU].
   - change(code_relation M rho(names k)x <->x=v). split;[intro HX;exact(code_relation_functional M _ rho x v HX HV)|intros ->;exact HV]. }
 exact(proj1(source_parameter_graph_ext M 3 source_rec_agreement_predicate source_rec_agreement_finite_bound(fun n=>names(sf_index(sigma n)))
  (source_finite_parameter_names 3)rho(source_rec_env3 f u v)HNames out)HG).
Qed.
Print Assumptions source_parameter_rec_agreement.
