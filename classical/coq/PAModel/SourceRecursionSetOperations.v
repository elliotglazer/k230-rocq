(** Literal fixed OP and Adj graphs used in one-pair extension of attempts. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterComposition SourceParameterGraphs SourceRecursionPrimitiveRelations.
From OldZF Require Std_setbase Std_setrec.
From OldZFC Require Z_rel.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_rec_ordered_pair_predicate:=isolated_formula(OldZF.Std_setbase.OP(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition source_rec_adjoin_predicate:=isolated_formula(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition source_rec_ordered_pair M x y q out:=code_relation M(source_rec_env3 x y q)
 (source_parameter_expression(source_finite_parameter_names 3)source_rec_ordered_pair_predicate)out.
Definition source_rec_adjoin M f q g out:=code_relation M(source_rec_env3 f q g)
 (source_parameter_expression(source_finite_parameter_names 3)source_rec_adjoin_predicate)out.
Lemma source_rec_ordered_pair_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 3 source_rec_ordered_pair_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 3(OldZF.Std_setbase.OP(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))).
 apply OldZFC.Z_rel.fb_bounded. OldZF.Std_setrec.fbsolve.
Qed.
Lemma source_rec_adjoin_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 3 source_rec_adjoin_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 3(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))).
 apply OldZFC.Z_rel.fb_bounded. unfold OldZF.Std_setbase.Adj. cbn. repeat split;lia.
Qed.
Theorem source_rec_ordered_pair_total M x y q:exists out,source_rec_ordered_pair M x y q out.
Proof. apply code_relation_total. Qed.
Theorem source_rec_adjoin_total M f q g:exists out,source_rec_adjoin M f q g out.
Proof. apply code_relation_total. Qed.
Lemma isolated_rec_ordered_pair_at t u v:
 isolated_formula(OldZF.Std_setbase.OP t u v)=C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))source_rec_ordered_pair_predicate.
Proof.
 pose proof(isolated_formula_subst(OldZF.Std_setbase.OP(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))
  (OC.scons t(OC.scons u(OC.scons v OC.var)))(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))ltac:(intros[|[|[|i]]];reflexivity))as HE.
 rewrite OldZF.Std_setbase.OP_subst in HE. exact HE.
Qed.
Lemma isolated_rec_adjoin_at t u v:
 isolated_formula(OldZF.Std_setbase.Adj t u v)=C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))source_rec_adjoin_predicate.
Proof.
 pose proof(isolated_formula_subst(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))
  (OC.scons t(OC.scons u(OC.scons v OC.var)))(C.scons(isolated_term t)(C.scons(isolated_term u)(C.scons(isolated_term v)C.var)))ltac:(intros[|[|[|i]]];reflexivity))as HE.
 rewrite OldZF.Std_setbase.Adj_subst in HE. exact HE.
Qed.
Theorem source_parameter_rec_ordered_pair M names rho i j k x y q out:
 code_relation M rho(names i)x ->code_relation M rho(names j)y ->code_relation M rho(names k)q ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setbase.OP(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j)(@OC.var OB.sig_empty k))))out ->
 source_rec_ordered_pair M x y q out.
Proof.
 intros HX HY HQ HG. rewrite isolated_rec_ordered_pair_at,source_parameter_substitution in HG.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))(C.scons(isolated_term(@OC.var OB.sig_empty k))C.var))).
 assert(HNames:forall n a,(n<3)%nat ->(code_relation M rho(names(sf_index(sigma n)))a <->code_relation M(source_rec_env3 x y q)(source_finite_parameter_names 3 n)a)).
 { intros[|[|[|n]]]a HN;try lia.
   - change(code_relation M rho(names i)a<->a=x). split;[intro H;exact(code_relation_functional M _ rho a x H HX)|intros ->;exact HX].
   - change(code_relation M rho(names j)a<->a=y). split;[intro H;exact(code_relation_functional M _ rho a y H HY)|intros ->;exact HY].
   - change(code_relation M rho(names k)a<->a=q). split;[intro H;exact(code_relation_functional M _ rho a q H HQ)|intros ->;exact HQ]. }
 exact(proj1(source_parameter_graph_ext M 3 source_rec_ordered_pair_predicate source_rec_ordered_pair_finite_bound(fun n=>names(sf_index(sigma n)))
  (source_finite_parameter_names 3)rho(source_rec_env3 x y q)HNames out)HG).
Qed.
Theorem source_parameter_rec_adjoin M names rho i j k f q g out:
 code_relation M rho(names i)f ->code_relation M rho(names j)q ->code_relation M rho(names k)g ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setbase.Adj(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j)(@OC.var OB.sig_empty k))))out ->
 source_rec_adjoin M f q g out.
Proof.
 intros HF HQ HH HG. rewrite isolated_rec_adjoin_at,source_parameter_substitution in HG.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))(C.scons(isolated_term(@OC.var OB.sig_empty k))C.var))).
 assert(HNames:forall n a,(n<3)%nat ->(code_relation M rho(names(sf_index(sigma n)))a <->code_relation M(source_rec_env3 f q g)(source_finite_parameter_names 3 n)a)).
 { intros[|[|[|n]]]a HN;try lia.
   - change(code_relation M rho(names i)a<->a=f). split;[intro H;exact(code_relation_functional M _ rho a f H HF)|intros ->;exact HF].
   - change(code_relation M rho(names j)a<->a=q). split;[intro H;exact(code_relation_functional M _ rho a q H HQ)|intros ->;exact HQ].
   - change(code_relation M rho(names k)a<->a=g). split;[intro H;exact(code_relation_functional M _ rho a g H HH)|intros ->;exact HH]. }
 exact(proj1(source_parameter_graph_ext M 3 source_rec_adjoin_predicate source_rec_adjoin_finite_bound(fun n=>names(sf_index(sigma n)))
  (source_finite_parameter_names 3)rho(source_rec_env3 f q g)HNames out)HG).
Qed.
Print Assumptions source_rec_ordered_pair_finite_bound.
Print Assumptions source_rec_adjoin_finite_bound.
Print Assumptions source_rec_ordered_pair_total.
Print Assumptions source_rec_adjoin_total.
Print Assumptions source_parameter_rec_ordered_pair.
Print Assumptions source_parameter_rec_adjoin.
