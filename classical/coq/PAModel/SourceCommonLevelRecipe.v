(** Literal common-level assertion for an internally finite parameter
    block: exists B exists Y [Ord(B) and LL(B,Y) and all parameters in Y]. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded NumericalInstantiation SourceMembershipBlocks SourceMembershipBlockProofs
  SourceHierarchySyntax SourceFiniteParameters SourceFiniteNameParameters SourceOrdinalPredicate.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_LL_literal_formula (d z out:term):form :=
  code_formula (source_parameter_expression (source_finite_parameter_names 2) source_LL_predicate)
    (fun (j:nat) =>match j with 0=>d|_=>z end) out.
Lemma source_LL_literal_formula_correct M rho d z out :
  holds M rho (source_LL_literal_formula d z out) <->
  source_LL_instance M (evalM M rho d)(evalM M rho z)(evalM M rho out).
Proof. unfold source_LL_literal_formula,source_LL_instance. rewrite code_formula_correct. reflexivity. Qed.

Definition source_common_level_data M ordcode start n out :=exists members ordinal level pair body exY,
  source_membership_block M (succM M(succM M start))(zeroM M) n members /\
  numerical_instantiation M ordcode(code_numeral M 1) ordinal /\
  source_LL_instance M (code_numeral M 1)(zeroM M) level /\
  sf_relation M SFAnd ordinal level pair /\sf_relation M SFAnd pair members body /\
  sf_relation M SFEx body (zeroM M) exY /\sf_relation M SFEx exY (zeroM M) out.
Definition source_common_level_recipe M start n out :=
  source_common_level_data M (source_ordinal_predicate_code M) start n out.
Definition source_common_lift6(t:term) :=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Definition source_common_level_formula (ordcode start n out:term):form :=
  ∃∃∃∃∃∃ (source_membership_block_formula (σ(σ(source_common_lift6 start))) zero (source_common_lift6 n) $5 ∧
    numerical_instantiation_formula (source_common_lift6 ordcode)(num 1) $4 ∧
    source_LL_literal_formula (num 1) zero $3 ∧sf_formula SFAnd $4 $3 $2 ∧sf_formula SFAnd $2 $5 $1 ∧
    sf_formula SFEx $1 zero $0 ∧sf_formula SFEx $0 zero (source_common_lift6 out)).
Lemma source_common_eval_lift6 M rho a b c d e f t :
  evalM M (a .: b .: c .: d .: e .: f .: rho)(source_common_lift6 t)=evalM M rho t.
Proof. unfold evalM,source_common_lift6. now rewrite !eval_up. Qed.
Lemma source_common_eval_succ M rho t :evalM M rho (σ t)=succM M(evalM M rho t).
Proof. reflexivity. Qed.
Local Opaque holds source_membership_block_formula numerical_instantiation_formula source_LL_literal_formula sf_formula.
Theorem source_common_level_formula_correct M rho ordcode start n out :
  holds M rho (source_common_level_formula ordcode start n out) <->
  source_common_level_data M (evalM M rho ordcode)(evalM M rho start)(evalM M rho n)(evalM M rho out).
Proof.
  unfold source_common_level_formula,source_common_level_data.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_membership_block_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct.
  setoid_rewrite source_LL_literal_formula_correct.
  setoid_rewrite sf_formula_correct.
  repeat setoid_rewrite source_common_eval_succ.
  setoid_rewrite source_common_eval_lift6.
  change ((exists members ordinal level pair body exY,
    (((((source_membership_block M (succM M(succM M(evalM M rho start)))(zeroM M)(evalM M rho n) members /\
      numerical_instantiation M (evalM M rho ordcode)(code_numeral M 1) ordinal) /\
      source_LL_instance M (code_numeral M 1)(zeroM M) level) /\sf_relation M SFAnd ordinal level pair) /\
      sf_relation M SFAnd pair members body) /\sf_relation M SFEx body (zeroM M) exY) /\
      sf_relation M SFEx exY (zeroM M)(evalM M rho out)) <->
    exists members ordinal level pair body exY,
      source_membership_block M (succM M(succM M(evalM M rho start)))(zeroM M)(evalM M rho n) members /\
      numerical_instantiation M (evalM M rho ordcode)(code_numeral M 1) ordinal /\
      source_LL_instance M (code_numeral M 1)(zeroM M) level /\sf_relation M SFAnd ordinal level pair /\
      sf_relation M SFAnd pair members body /\sf_relation M SFEx body (zeroM M) exY /\
      sf_relation M SFEx exY (zeroM M)(evalM M rho out)).
  split;intros [members [ordinal [level [pair [body [exY H]]]]]];
    exists members,ordinal,level,pair,body,exY;tauto.
Qed.

Theorem source_common_level_recipe_total M start n :exists out,source_common_level_recipe M start n out.
Proof.
  destruct (source_membership_block_total M (succM M(succM M start))(zeroM M) n) as [members HM].
  destruct (numerical_instantiation_total M (source_ordinal_predicate_code M)(code_numeral M 1)) as [ordinal HO].
  destruct (source_LL_instance_total M (code_numeral M 1)(zeroM M)) as [level HL].
  destruct (sf_relation_total M SFAnd ordinal level) as [pair HP].
  destruct (sf_relation_total M SFAnd pair members) as [body HB].
  destruct (sf_relation_total M SFEx body (zeroM M)) as [exY HY].
  destruct (sf_relation_total M SFEx exY (zeroM M)) as [out HF].
  exists out,members,ordinal,level,pair,body,exY. repeat first [assumption|split].
Qed.
Theorem source_common_level_recipe_functional M start n f g :
  source_common_level_recipe M start n f ->source_common_level_recipe M start n g ->f=g.
Proof.
  intros (members&ordinal&level&pair&body&exY&HM&HO&HL&HP&HB&HY&HF)
    (members'&ordinal'&level'&pair'&body'&exY'&HM'&HO'&HL'&HP'&HB'&HY'&HG).
  pose proof (source_membership_block_functional M (succM M(succM M start))(zeroM M) n members members' HM HM') as E. subst members'.
  pose proof (numerical_instantiation_functional M (source_ordinal_predicate_code M)(code_numeral M 1) ordinal ordinal' HO HO') as E. subst ordinal'.
  pose proof (source_LL_instance_functional M (code_numeral M 1)(zeroM M) level level' HL HL') as E. subst level'.
  pose proof (sf_relation_functional M SFAnd ordinal level pair pair' HP HP') as E. subst pair'.
  pose proof (sf_relation_functional M SFAnd pair members body body' HB HB') as E. subst body'.
  pose proof (sf_relation_functional M SFEx body (zeroM M) exY exY' HY HY') as E. subst exY'.
  exact (sf_relation_functional M SFEx exY (zeroM M) f g HF HG).
Qed.

Print Assumptions source_LL_literal_formula_correct.
Print Assumptions source_common_level_formula_correct.
Print Assumptions source_common_level_recipe_total.
Print Assumptions source_common_level_recipe_functional.
