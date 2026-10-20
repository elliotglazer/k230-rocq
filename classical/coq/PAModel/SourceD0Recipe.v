(** Exact D0f witness-closure recipe, with the fixed level predicate LL(1,0)
    supplied as a source code. All matrix codes and bounds are internal. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceBoundMonotone SourceFiniteCutoffShift SourceRelativizationRules SourceRelativizationBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_cutoff_shift_thrice M phi out := exists first second,
  source_cutoff_shift M 1 phi first /\ source_cutoff_shift M 1 first second /\ source_cutoff_shift M 1 second out.
Definition source_cutoff_shift_thrice_formula (phi out:term) : form :=
  ∃∃ (source_cutoff_shift_formula 1 (code_lift2 phi) $1 ∧
    (source_cutoff_shift_formula 1 $1 $0 ∧ source_cutoff_shift_formula 1 $0 (code_lift2 out))).
Local Opaque holds source_cutoff_shift_formula.
Theorem source_cutoff_shift_thrice_formula_correct M rho phi out :
  holds M rho (source_cutoff_shift_thrice_formula phi out) <->
  source_cutoff_shift_thrice M (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_cutoff_shift_thrice_formula,source_cutoff_shift_thrice. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite source_cutoff_shift_formula_correct.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Theorem source_cutoff_shift_thrice_total M phi : exists out,source_cutoff_shift_thrice M phi out.
Proof.
  destruct (source_cutoff_shift_total M 1 phi) as [first H1].
  destruct (source_cutoff_shift_total M 1 first) as [second H2].
  destruct (source_cutoff_shift_total M 1 second) as [out H3]. exists out,first,second. auto.
Qed.
Theorem source_cutoff_shift_thrice_bounded M phi out n :
  source_bounded M phi (succM M n) -> source_cutoff_shift_thrice M phi out ->
  source_bounded M out (succM M (succM M (succM M (succM M n)))).
Proof.
  intros HP (first & second & H1 & H2 & H3).
  exact (source_cutoff_shift_bounded M 1 second out (succM M (succM M n))
    (source_cutoff_shift_bounded M 1 first second (succM M n)
      (source_cutoff_shift_bounded M 1 phi first n HP H1) H2) H3).
Qed.

Definition source_ew_recipe M domain matrix out := exists atom left right,
  sf_relation M SFMember (zeroM M) (code_numeral M 1) atom /\
  sr_quantifier M false domain matrix left /\ sr_quantifier M false atom matrix right /\
  sf_relation M SFImpl left right out.
Definition source_ew_recipe_formula (domain matrix out:term) : form :=
  ∃∃∃ (sf_formula SFMember zero (num 1) $2 ∧
    (sr_quantifier_formula false (lift3 domain) (lift3 matrix) $1 ∧
    (sr_quantifier_formula false $2 (lift3 matrix) $0 ∧ sf_formula SFImpl $1 $0 (lift3 out)))).
Local Opaque sf_formula sr_quantifier_formula.
Theorem source_ew_recipe_formula_correct M rho domain matrix out :
  holds M rho (source_ew_recipe_formula domain matrix out) <->
  source_ew_recipe M (evalM M rho domain) (evalM M rho matrix) (evalM M rho out).
Proof.
  unfold source_ew_recipe_formula,source_ew_recipe. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite sf_formula_correct. setoid_rewrite sr_quantifier_formula_correct.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_ew_recipe_total M domain matrix : exists out,source_ew_recipe M domain matrix out.
Proof.
  destruct (sf_relation_total M SFMember (zeroM M) (code_numeral M 1)) as [atom HA].
  destruct (sr_quantifier_total M false domain matrix) as [left HL].
  destruct (sr_quantifier_total M false atom matrix) as [right HR].
  destruct (sf_relation_total M SFImpl left right) as [out HO]. exists out,atom,left,right. auto.
Qed.

Lemma source_guarded_exists_bounded M guard matrix out k :
  source_bounded M guard (succM M k) -> source_bounded M matrix (succM M k) ->
  sr_quantifier M false guard matrix out -> source_bounded M out k.
Proof.
  intros HG HM [body [HB HO]].
  apply (proj2 (source_bounded_accept_unary M SFEx body out k (or_intror eq_refl) HO)).
  apply (proj2 (source_bounded_accept_binary M SFAnd guard matrix body (succM M k) (or_introl eq_refl) HB)). auto.
Qed.

Theorem source_ew_recipe_bounded M domain matrix out n :
  source_bounded M domain (code_numeral M 1) -> source_bounded M matrix (succM M (succM M n)) ->
  source_ew_recipe M domain matrix out -> source_bounded M out (succM M n).
Proof.
  intros HD HM (atom & left & right & HA & HL & HR & HO).
  apply (proj2 (source_bounded_accept_binary M SFImpl left right out (succM M n)
    (or_intror (or_intror eq_refl)) HO)). split.
  - exact (source_guarded_exists_bounded M domain matrix left (succM M n)
      (sr_domain_bound_succ M domain (succM M n) HD) HM HL).
  - apply (source_guarded_exists_bounded M atom matrix right (succM M n));[|exact HM|exact HR].
    apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 1) atom
      (succM M (succM M n)) (or_introl eq_refl) HA)). split.
    + apply coding_zero_lt_succ.
    + apply coding_lt_succ_cancel,coding_zero_lt_succ.
Qed.

Definition source_d0_recipe M domain level body out := exists shifted ew implication,
  source_cutoff_shift_thrice M body shifted /\ source_ew_recipe M domain shifted ew /\
  sf_relation M SFImpl level ew implication /\ sf_relation M SFAll implication (zeroM M) out.
Definition source_d0_recipe_formula (domain level body out:term) : form :=
  ∃∃∃ (source_cutoff_shift_thrice_formula (lift3 body) $2 ∧
    (source_ew_recipe_formula (lift3 domain) $2 $1 ∧
    (sf_formula SFImpl (lift3 level) $1 $0 ∧ sf_formula SFAll $0 zero (lift3 out)))).
Local Opaque source_cutoff_shift_thrice_formula source_ew_recipe_formula.
Theorem source_d0_recipe_formula_correct M rho domain level body out :
  holds M rho (source_d0_recipe_formula domain level body out) <->
  source_d0_recipe M (evalM M rho domain) (evalM M rho level) (evalM M rho body) (evalM M rho out).
Proof.
  unfold source_d0_recipe_formula,source_d0_recipe. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_cutoff_shift_thrice_formula_correct. setoid_rewrite source_ew_recipe_formula_correct.
  setoid_rewrite sf_formula_correct. unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_d0_recipe_total M domain level body : exists out,source_d0_recipe M domain level body out.
Proof.
  destruct (source_cutoff_shift_thrice_total M body) as [shifted HS].
  destruct (source_ew_recipe_total M domain shifted) as [ew HE].
  destruct (sf_relation_total M SFImpl level ew) as [implication HI].
  destruct (sf_relation_total M SFAll implication (zeroM M)) as [out HO].
  exists out,shifted,ew,implication. auto.
Qed.
Theorem source_d0_recipe_bounded M domain level body out n :
  source_bounded M domain (code_numeral M 1) -> source_bounded M level (code_numeral M 2) ->
  source_bounded M body (succM M n) -> source_d0_recipe M domain level body out ->
  source_bounded M out (succM M (succM M n)).
Proof.
  intros HD HL HB (shifted & ew & implication & HS & HE & HI & HO).
  apply (proj2 (source_bounded_accept_unary M SFAll implication out (succM M (succM M n)) (or_introl eq_refl) HO)).
  apply (proj2 (source_bounded_accept_binary M SFImpl level ew implication (succM M (succM M (succM M n)))
    (or_intror (or_intror eq_refl)) HI)). split.
  - apply (source_bounded_monotone M level (code_numeral M 2) (succM M (succM M (succM M n))) HL).
    apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ.
  - exact (source_ew_recipe_bounded M domain shifted ew (succM M (succM M n)) HD
      (source_cutoff_shift_thrice_bounded M body shifted n HB HS) HE).
Qed.

Print Assumptions source_cutoff_shift_thrice_formula_correct.
Print Assumptions source_cutoff_shift_thrice_bounded.
Print Assumptions source_ew_recipe_formula_correct.
Print Assumptions source_ew_recipe_bounded.
Print Assumptions source_d0_recipe_formula_correct.
Print Assumptions source_d0_recipe_total.
Print Assumptions source_d0_recipe_bounded.
