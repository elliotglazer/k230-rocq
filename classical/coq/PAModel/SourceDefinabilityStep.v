(** Exact recursive syntax steps for the EnvF and NumF prerequisites of
    Z_cl.rep_ex. The environment case keeps e at0 and inserts two slots
    before the remaining parameters, exactly as EnvF_S requires. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 SetFormulaCodes SourceBounded SourceBoundMonotone SourceDefinabilityPrimitives
 SourceFiniteCutoffShift SourceQfFunctionality NumericalProofs SubstitutionSource SchemaConstructorBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_def_step_expression (environment:bool) :code_expr :=
 E_sf SFEx (E_sf SFAnd (CEvar 0)
  (CEconst(sf_encode(if environment then source_def_extension021 else source_def_successor01)))) (CEconst 0).
Definition source_def_step M (environment:bool) previous out :=exists shifted,
 (if environment then exists middle,source_cutoff_shift M 1 previous middle /\
    source_cutoff_shift M 1 middle shifted else shifted=previous) /\
 code_relation M(fun _=>shifted)(source_def_step_expression environment) out.
Definition source_def_step_formula (environment:bool)(previous out:term) :form :=
 ∃ ((if environment then ∃(source_cutoff_shift_formula 1 previous`[↑]`[↑] $0 ∧
       source_cutoff_shift_formula 1 $0 $1) else $0==previous`[↑]) ∧
  code_formula(source_def_step_expression environment)(fun _=>$0) out`[↑]).
Lemma source_def_equality_correct M rho(t u:term) :holds M rho(t==u)<->evalM M rho t=evalM M rho u.
Proof. reflexivity. Qed.
Local Opaque holds source_cutoff_shift_formula code_formula.
Theorem source_def_step_formula_correct M environment rho previous out :
 holds M rho(source_def_step_formula environment previous out) <->
 source_def_step M environment(evalM M rho previous)(evalM M rho out).
Proof.
 unfold source_def_step_formula,source_def_step. rewrite holds_ex.
 setoid_rewrite holds_and. setoid_rewrite code_formula_correct.
 destruct environment;cbn.
 - setoid_rewrite holds_ex. setoid_rewrite holds_and.
   setoid_rewrite source_cutoff_shift_formula_correct.
   unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
 - setoid_rewrite source_def_equality_correct. unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_def_step_total M environment previous :exists out,source_def_step M environment previous out.
Proof.
 destruct environment.
 - destruct(source_cutoff_shift_total M 1 previous)as(middle&HM).
   destruct(source_cutoff_shift_total M 1 middle)as(shifted&HS).
   destruct(code_relation_total M(source_def_step_expression true)(fun _=>shifted))as(out&HO).
   exists out,shifted. split;[exists middle;auto|exact HO].
 - destruct(code_relation_total M(source_def_step_expression false)(fun _=>previous))as(out&HO).
   exists out,previous. split;[reflexivity|exact HO].
Qed.
Theorem source_def_step_functional M environment previous out other :
 source_def_step M environment previous out ->source_def_step M environment previous other ->out=other.
Proof.
 intros(s&HS&HO)(t&HT&HP).
 assert(E:s=t).
 { destruct environment.
   - destruct HS as(m&HM&HS),HT as(n&HN&HT).
     assert(m=n)by(eapply source_cutoff_shift_functional;eassumption). subst n.
     eapply source_cutoff_shift_functional;eassumption.
   - congruence. }
 subst t. eapply code_relation_functional;eassumption.
Qed.
Lemma source_def_step_graph M environment previous out :
 source_def_step M environment previous out ->exists shifted middle,
 (if environment then exists intermediate,source_cutoff_shift M 1 previous intermediate /\
   source_cutoff_shift M 1 intermediate shifted else shifted=previous) /\
 sf_relation M SFAnd shifted(code_numeral M(sf_encode
   (if environment then source_def_extension021 else source_def_successor01))) middle /\
 sf_relation M SFEx middle(zeroM M) out.
Proof.
 intros(s&HS&HO). destruct(code_relation_total M
  (E_sf SFAnd(CEvar 0)(CEconst(sf_encode(if environment then source_def_extension021 else source_def_successor01))))
  (fun _=>s))as(m&HM).
 exists s,m. split;[exact HS|]. split.
 - exact(proj1(schema_expression_graph M(fun _=>s) SFAnd (CEvar 0) (CEconst(sf_encode(if environment then source_def_extension021 else source_def_successor01))) s _ m eq_refl eq_refl) HM).
 - exact(proj1(schema_expression_graph M(fun _=>s) SFEx (E_sf SFAnd(CEvar 0)(CEconst(sf_encode(if environment then source_def_extension021 else source_def_successor01)))) (CEconst 0) m (zeroM M) out HM eq_refl) HO).
Qed.
Theorem source_def_numeral_step_bound M previous out :
 source_bounded M previous(code_numeral M 1) ->source_def_step M false previous out ->
 source_bounded M out(code_numeral M 1).
Proof.
 intros HP HS. destruct(source_def_step_graph M false previous out HS)as(s&m&ES&HM&HO).
 subst s. apply(proj2(source_bounded_accept_unary M SFEx m out(code_numeral M 1)(or_intror eq_refl) HO)).
 apply(proj2(source_bounded_accept_binary M SFAnd previous _ m(code_numeral M 2)(or_introl eq_refl) HM)).
 split;[|apply numerical_def_successor_bound].
 apply(source_bounded_monotone M previous(code_numeral M 1)(code_numeral M 2) HP).
 apply coding_lt_succ_cancel,coding_zero_lt_succ.
Qed.
Theorem source_def_environment_step_bound M n previous out :
 source_bounded M previous(succM M n) ->source_def_step M true previous out ->
 source_bounded M out(succM M(succM M n)).
Proof.
 intros HP HStep. destruct(source_def_step_graph M true previous out HStep)as(s&m&(q&HQ&HS)&HM&HO).
 apply(proj2(source_bounded_accept_unary M SFEx m out(succM M(succM M n))(or_intror eq_refl) HO)).
 apply(proj2(source_bounded_accept_binary M SFAnd s _ m(succM M(succM M(succM M n)))(or_introl eq_refl) HM)).
 split.
 - exact(source_cutoff_shift_bounded M 1 q s(succM M n)
     (source_cutoff_shift_bounded M 1 previous q n HP HQ) HS).
 - apply(source_bounded_monotone M _ (code_numeral M 3) _ (numerical_def_extension_bound M)).
   do 3 apply coding_lt_succ_cancel. apply coding_zero_lt_succ.
Qed.
Print Assumptions source_def_step_formula_correct.
Print Assumptions source_def_step_total.
Print Assumptions source_def_step_functional.
Print Assumptions source_def_numeral_step_bound.
Print Assumptions source_def_environment_step_bound.

