(** The fixed Rel2(phSig) compiler is exactly the shared successor graph. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterComposition SourceParameterGraphs SourceRecursionPrimitiveRelations.
From OldZF Require Std_setrec Std_setinf.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Lemma isolated_rec_rel2_successor_at t u:
 isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig t u)=
 C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)(fun _=>isolated_term t)))source_rec_successor_predicate.
Proof.
 exact(isolated_formula_subst OldZF.Std_setinf.phSig(OC.scons t(OC.scons u(fun _=>t)))
  (C.scons(isolated_term t)(C.scons(isolated_term u)(fun _=>isolated_term t)))ltac:(intros[|[|i]];reflexivity)).
Qed.
Theorem source_parameter_rec_rel2_successor M names rho i j z v out:
 code_relation M rho(names i)z ->code_relation M rho(names j)v ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig
  (@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j))))out ->source_rec_successor M z v out.
Proof.
 intros HZ HV HG. rewrite isolated_rec_rel2_successor_at,source_parameter_substitution in HG.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))(fun _=>isolated_term(@OC.var OB.sig_empty i)))).
 assert(HNames:forall n x,(n<2)%nat ->(code_relation M rho(names(sf_index(sigma n)))x <->
  code_relation M(source_rec_env2 z v)(source_finite_parameter_names 2 n)x)).
 { intros[|[|n]]x HN;try lia.
   - change(code_relation M rho(names i)x <->x=z). split;[intro HX;exact(code_relation_functional M _ rho x z HX HZ)|intros ->;exact HZ].
   - change(code_relation M rho(names j)x <->x=v). split;[intro HX;exact(code_relation_functional M _ rho x v HX HV)|intros ->;exact HV]. }
 exact(proj1(source_parameter_graph_ext M 2 source_rec_successor_predicate source_rec_successor_finite_bound(fun n=>names(sf_index(sigma n)))
  (source_finite_parameter_names 2)rho(source_rec_env2 z v)HNames out)HG).
Qed.
Print Assumptions isolated_rec_rel2_successor_at.
Print Assumptions source_parameter_rec_rel2_successor.
