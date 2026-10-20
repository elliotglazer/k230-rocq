(** Exact successor/quantifier maps for the internal NumF comparison recursion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceBounded SourceQuantifierRules SourceFiniteCutoffShift SourceCutoffPropositional SourceCutoffQuantifiers
 SourceDefinabilityPrimitives SourceDefinabilityStep SourceNumFClosureFiniteShells SourceNumFClosureRecipe
 SourceNumFComparisonFixed SourcePropositionalTemplates SourceLeastOrdinalWitness
 OldNamedSyntaxBridge OldFullNDSourceBridge NumericalRenaming.
From OldZFC Require Z_base.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition numf_successor02 :sf_form :=source_def_successor01[source_shift_sigma 1].
Definition numf_successor03 :sf_form :=numf_successor02[source_shift_sigma 1].
Lemma numf_successor02_shape :numf_successor02=isolated_formula(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)).
Proof.
 unfold numf_successor02,source_def_successor01.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))
  (fun idx=>match idx with 0=>@OC.var OB.sig_empty 0|S j=>@OC.var OB.sig_empty(S(S j))end)
  (source_shift_sigma 1)ltac:(intros[|idx];reflexivity))as E.
 rewrite OldZFC.Z_base.Succ0_subst in E. exact(eq_sym E).
Qed.
Lemma numf_successor03_shape :numf_successor03=isolated_formula(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 3)).
Proof.
 unfold numf_successor03. rewrite numf_successor02_shape.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2))
  (fun idx=>match idx with 0=>@OC.var OB.sig_empty 0|S j=>@OC.var OB.sig_empty(S(S j))end)
  (source_shift_sigma 1)ltac:(intros[|idx];reflexivity))as E.
 rewrite OldZFC.Z_base.Succ0_subst in E. exact(eq_sym E).
Qed.
Lemma numf_successor_square_shape :source_numf_successor_square_law=
 ($0 ≡' $1 →numf_closure_succ_shift_form →numf_successor03 →$2 ≡' $3).
Proof. rewrite numf_successor03_shape. reflexivity. Qed.
Theorem source_numf_successor_cutoffs M :
 source_cutoff_shift M 1(code_numeral M(sf_encode source_def_successor01))(code_numeral M(sf_encode numf_successor02)) /\
 source_cutoff_shift M 1(code_numeral M(sf_encode numf_successor02))(code_numeral M(sf_encode numf_successor03)).
Proof.
 split;[apply(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M)source_def_successor01)|
 apply(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M)numf_successor02)];apply source_formula_numeral_graph.
Qed.
Theorem source_numf_unary_exists_shift M p s t pair other ex nex :source_bounded M p(code_numeral M 1) ->
 source_cutoff_shift M 1 s t ->sf_relation M SFAnd p s pair ->sf_relation M SFAnd p t other ->
 sf_relation M SFEx pair(zeroM M)ex ->sf_relation M SFEx other(zeroM M)nex ->source_formula_shift M ex nex.
Proof.
 intros BP HS HB HO HE HN. apply source_cutoff_zero_is_shift.
 apply(source_cutoff_quantifier_join M 0 false pair other ex nex HE HN).
 set(env:=sf_env p s). set(otherenv:=sf_env p t).
 apply(source_cutoff_shift_propositional M 1 env otherenv(SPTAnd(SPTSlot 0)(SPTSlot 1))pair other).
 - intros[|idx];cbn[env otherenv sf_env];[exact(source_cutoff_shift_fixes_domain M 0 p BP)|exact HS].
 - eapply source_prop_template_join;[reflexivity|reflexivity|exact HB].
 - eapply source_prop_template_join;[reflexivity|reflexivity|exact HO].
Qed.
Theorem source_numf_step_comparison_structure M p q :source_bounded M p(code_numeral M 1) ->source_def_step M false p q ->
 exists ps pair shifted pair2 pair3 q1 q2,
 source_formula_shift M p ps /\
 sf_relation M SFAnd p(code_numeral M(sf_encode source_def_successor01))pair /\sf_relation M SFEx pair(zeroM M)q /\
 sf_relation M SFAnd ps(numf_closure_succ_shift_code M)shifted /\source_formula_shift M pair shifted /\
 sf_relation M SFAnd p(code_numeral M(sf_encode numf_successor02))pair2 /\sf_relation M SFEx pair2(zeroM M)q1 /\source_formula_shift M q q1 /\
 sf_relation M SFAnd p(code_numeral M(sf_encode numf_successor03))pair3 /\sf_relation M SFEx pair3(zeroM M)q2 /\source_formula_shift M q1 q2.
Proof.
 intros BP HStep. destruct(source_def_step_graph M false p q HStep)as(unused&pair&EU&HP&HQ). subst unused.
 destruct(numerical_renaming_total M p(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(ps&HPS).
 destruct(sf_relation_total M SFAnd ps(numf_closure_succ_shift_code M))as(shifted&HS).
 destruct(sf_relation_total M SFAnd p(code_numeral M(sf_encode numf_successor02)))as(pair2&HP2).
 destruct(sf_relation_total M SFAnd p(code_numeral M(sf_encode numf_successor03)))as(pair3&HP3).
 destruct(sf_relation_total M SFEx pair2(zeroM M))as(q1&HQ1).
 destruct(sf_relation_total M SFEx pair3(zeroM M))as(q2&HQ2).
 destruct(source_numf_successor_cutoffs M)as(H12&H23).
 exists ps,pair,shifted,pair2,pair3,q1,q2.
 split;[exact HPS|]. split;[exact HP|]. split;[exact HQ|]. split;[exact HS|].
 split;[exact(source_formula_shift_conjunction M p _ pair ps _ shifted HP HS HPS(source_numf_closure_succ_shift M))|].
 split;[exact HP2|]. split;[exact HQ1|].
 split;[exact(source_numf_unary_exists_shift M p _ _ pair pair2 q q1 BP H12 HP HP2 HQ HQ1)|].
 split;[exact HP3|]. split;[exact HQ2|].
 exact(source_numf_unary_exists_shift M p _ _ pair2 pair3 q1 q2 BP H23 HP2 HP3 HQ1 HQ2).
Qed.
Print Assumptions source_numf_step_comparison_structure.
