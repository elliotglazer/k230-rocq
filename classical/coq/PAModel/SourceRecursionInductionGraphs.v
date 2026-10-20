(** Named STot and SInd graphs for the pinned fixed successor relation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteParameterComposition SourceFiniteNameParameters SourceParameterGraphs SourceRecursionPrimitiveRelations.
From OldZF Require Std_setinf Std_setrec.
From OldZFC Require Z_rel.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_rec_totality_predicate:sf_form:=isolated_formula(OldZF.Std_setrec.STot OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)).
Definition source_rec_induction_predicate:sf_form:=isolated_formula(OldZF.Std_setrec.SInd OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Definition source_rec_totality M N out:=code_relation M(fun _=>N)
 (source_parameter_expression(source_finite_parameter_names 1)source_rec_totality_predicate)out.
Definition source_rec_induction M o N out:=code_relation M(source_rec_env2 o N)
 (source_parameter_expression(source_finite_parameter_names 2)source_rec_induction_predicate)out.
Lemma source_rec_totality_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 1 source_rec_totality_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 1(OldZF.Std_setrec.STot OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Lemma source_rec_induction_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 2 source_rec_induction_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 2(OldZF.Std_setrec.SInd OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_rec_totality_total M N:exists out,source_rec_totality M N out.
Proof. apply code_relation_total. Qed.
Theorem source_rec_induction_total M o N:exists out,source_rec_induction M o N out.
Proof. apply code_relation_total. Qed.
Lemma isolated_rec_totality_at t:isolated_formula(OldZF.Std_setrec.STot OldZF.Std_setinf.phSig t)=
 C.subst_form(C.scons(isolated_term t)C.var)source_rec_totality_predicate.
Proof.
 pose proof(isolated_formula_subst(OldZF.Std_setrec.STot OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0))
  (OC.scons t OC.var)(C.scons(isolated_term t)C.var)ltac:(intros[|i];reflexivity))as HE.
 rewrite OldZF.Std_setrec.STot_subst in HE. exact HE.
Qed.
Lemma isolated_rec_induction_at t u:isolated_formula(OldZF.Std_setrec.SInd OldZF.Std_setinf.phSig t u)=
 C.subst_form(C.scons(isolated_term t)(C.scons(isolated_term u)C.var))source_rec_induction_predicate.
Proof.
 pose proof(isolated_formula_subst(OldZF.Std_setrec.SInd OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))
  (OC.scons t(OC.scons u OC.var))(C.scons(isolated_term t)(C.scons(isolated_term u)C.var))ltac:(intros[|[|i]];reflexivity))as HE.
 rewrite OldZF.Std_setrec.SInd_subst in HE. exact HE.
Qed.
Theorem source_parameter_rec_totality M names rho i N out:code_relation M rho(names i)N ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setrec.STot OldZF.Std_setinf.phSig(@OC.var OB.sig_empty i))))out ->
 source_rec_totality M N out.
Proof.
 intros HN HG. rewrite isolated_rec_totality_at,source_parameter_substitution in HG.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))C.var).
 assert(HNames:forall n x,(n<1)%nat ->(code_relation M rho(names(sf_index(sigma n)))x <->
  code_relation M(fun _=>N)(source_finite_parameter_names 1 n)x)).
 { intros[|idx] x HX;[|lia]. change(code_relation M rho(names i)x<->x=N).
   split;[intro H;exact(code_relation_functional M _ rho x N H HN)|intros ->;exact HN]. }
 exact(proj1(source_parameter_graph_ext M 1 source_rec_totality_predicate source_rec_totality_finite_bound
  (fun n=>names(sf_index(sigma n)))(source_finite_parameter_names 1)rho(fun _=>N)HNames out)HG).
Qed.
Theorem source_parameter_rec_induction M names rho i j o N out:code_relation M rho(names i)o ->code_relation M rho(names j)N ->
 code_relation M rho(source_parameter_expression names(isolated_formula(OldZF.Std_setrec.SInd OldZF.Std_setinf.phSig(@OC.var OB.sig_empty i)(@OC.var OB.sig_empty j))))out ->
 source_rec_induction M o N out.
Proof.
 intros HO HN HG. rewrite isolated_rec_induction_at,source_parameter_substitution in HG.
 set(sigma:=C.scons(isolated_term(@OC.var OB.sig_empty i))(C.scons(isolated_term(@OC.var OB.sig_empty j))C.var)).
 assert(HNames:forall n x,(n<2)%nat ->(code_relation M rho(names(sf_index(sigma n)))x <->
  code_relation M(source_rec_env2 o N)(source_finite_parameter_names 2 n)x)).
 { intros[|[|idx]] x HX;try lia.
   - change(code_relation M rho(names i)x<->x=o). split;[intro H;exact(code_relation_functional M _ rho x o H HO)|intros ->;exact HO].
   - change(code_relation M rho(names j)x<->x=N). split;[intro H;exact(code_relation_functional M _ rho x N H HN)|intros ->;exact HN]. }
 exact(proj1(source_parameter_graph_ext M 2 source_rec_induction_predicate source_rec_induction_finite_bound
  (fun n=>names(sf_index(sigma n)))(source_finite_parameter_names 2)rho(source_rec_env2 o N)HNames out)HG).
Qed.
Print Assumptions source_rec_totality_finite_bound.
Print Assumptions source_rec_induction_finite_bound.
Print Assumptions source_rec_totality_total.
Print Assumptions source_rec_induction_total.
Print Assumptions source_parameter_rec_totality.
Print Assumptions source_parameter_rec_induction.
