(** Exact finite conditions in the uniform NumF-in-C induction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceBounded SourceBoundMonotone SourceImplicationAllShift SourceQuantifierRules
 SourceDefinabilityPrimitives SourceDefinabilitySuccessor SourceRepresentationClosureRecipe
 SourceNumFClosureSuccessorPointFixed SourceNumFClosureSyntax OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceZFRProvability.
From OldZFC Require Z_base Z_cl.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition numf_closure_succ_shift_form :sf_form :=isolated_formula(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition numf_closure_condition_shift_form :sf_form :=isolated_formula(OldZFC.Z_cl.Cl(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)).
Lemma numf_closure_succ_form_shift :source_def_successor01[↑]=numf_closure_succ_shift_form.
Proof.
 unfold source_def_successor01,numf_closure_succ_shift_form.
 pose proof(isolated_old_formula_shift(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)))as E.
 rewrite OldZFC.Z_base.Succ0_subst in E. exact(eq_sym E).
Qed.
Lemma numf_closure_condition_form_shift :representation_closure_condition[↑]=numf_closure_condition_shift_form.
Proof.
 unfold representation_closure_condition,numf_closure_condition_shift_form.
 pose proof(isolated_old_formula_shift(OldZFC.Z_cl.Cl(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)))as E.
 rewrite OldZFC.Z_cl.Cl_subst in E. exact(eq_sym E).
Qed.
Lemma numf_closure_succ10_shape :source_def_succ10=isolated_formula(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)).
Proof.
 unfold source_def_succ10,source_def_successor01.
 pose proof(isolated_old_formula_instantiate(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))(@OC.var OB.sig_empty 1))as E.
 rewrite OldZFC.Z_base.Succ0_subst in E. exact(eq_sym E).
Qed.
Lemma numf_closure_successor_point_shape :source_numf_closure_successor_point=
 (numf_closure_succ_shift_form →numf_closure_condition_shift_form →$0 ∈' $3 →∃(source_def_succ10 ∧$0 ∈' $4)).
Proof. rewrite numf_closure_succ10_shape. reflexivity. Qed.
Definition numf_closure_succ_shift_code M :=code_numeral M(sf_encode numf_closure_succ_shift_form).
Definition numf_closure_condition_shift_code M :=code_numeral M(sf_encode numf_closure_condition_shift_form).
Theorem source_numf_closure_succ_shift M :source_formula_shift M
 (code_numeral M(sf_encode source_def_successor01))(numf_closure_succ_shift_code M).
Proof. unfold numf_closure_succ_shift_code. rewrite <-numf_closure_succ_form_shift. apply source_formula_numeral_shift. Qed.
Theorem source_numf_closure_condition_shift M :source_formula_shift M
 (code_numeral M(sf_encode representation_closure_condition))(numf_closure_condition_shift_code M).
Proof. unfold numf_closure_condition_shift_code. rewrite <-numf_closure_condition_form_shift. apply source_formula_numeral_shift. Qed.
Theorem source_numf_closure_successor_point_shell M :exists body ex tail middle law,
 sf_relation M SFAnd(code_numeral M(sf_encode source_def_succ10))(source_numf_closure_member M 4)body /\
 sf_relation M SFEx body(zeroM M)ex /\
 sf_relation M SFImpl(source_numf_closure_member M 3)ex tail /\
 sf_relation M SFImpl(numf_closure_condition_shift_code M)tail middle /\
 sf_relation M SFImpl(numf_closure_succ_shift_code M)middle law /\source_zfr_provable M law.
Proof.
 set(s:=sf_encode source_def_succ10). set(m3:=sf_make SFMember 0 3). set(m4:=sf_make SFMember 0 4).
 set(b:=sf_make SFAnd s m4). set(e:=sf_make SFEx b 0). set(t:=sf_make SFImpl m3 e).
 set(c:=sf_encode numf_closure_condition_shift_form). set(a:=sf_encode numf_closure_succ_shift_form).
 set(j:=sf_make SFImpl c t). set(l:=sf_make SFImpl a j).
 exists(code_numeral M b),(code_numeral M e),(code_numeral M t),(code_numeral M j),(code_numeral M l).
 split;[exact(sf_make_numeral M SFAnd s m4)|]. split;[exact(sf_make_numeral M SFEx b 0)|].
 split;[exact(sf_make_numeral M SFImpl m3 e)|]. split;[exact(sf_make_numeral M SFImpl c t)|].
 split;[exact(sf_make_numeral M SFImpl a j)|].
 pose proof(source_zfr_numf_closure_successor_point M)as P.
 rewrite numf_closure_successor_point_shape in P. exact P.
Qed.
Print Assumptions source_numf_closure_succ_shift.
Print Assumptions source_numf_closure_condition_shift.
Print Assumptions source_numf_closure_successor_point_shell.
