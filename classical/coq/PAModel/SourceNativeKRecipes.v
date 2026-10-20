(** Exact canonical output-root and K-prime source syntax. The only matrix
    input is an arbitrary internally coded phi, with output0/input1 roles. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
  SourceQuantifierRules SourceNumeralLift SourceNativeKShifts SourceEmittedClosureRecipe SourceImplicationAllShift.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Sets.minZF.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_upper_conclusion_recipe M phi out :=exists p h shifted atom root body,
  source_formula_shift M phi p /\source_emitted_closure_recipe M phi h /\
  source_native_k_upshift M h shifted /\sf_relation M SFMember (code_numeral M 1)(zeroM M) atom /\
  sf_relation M SFImpl p atom root /\sf_relation M SFAnd root shifted body /\sf_relation M SFEx body (zeroM M) out.
Definition native_lift6 (t:term) :=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Definition source_upper_conclusion_recipe_formula (phi out:term) :form :=
  ∃∃∃∃∃∃ (numerical_renaming_formula (native_lift6 phi) zero zero zero (num 1) $5 ∧
    (source_emitted_closure_recipe_formula (native_lift6 phi) $4 ∧
    (numerical_renaming_formula $4 zero zero (num 1)(num 1) $3 ∧
    (sf_formula SFMember (num 1) zero $2 ∧
    (sf_formula SFImpl $5 $2 $1 ∧
    (sf_formula SFAnd $1 $3 $0 ∧sf_formula SFEx $0 zero (native_lift6 out))))))).
Definition source_kprime_core_recipe M phi out :=exists upper all1,
  source_upper_conclusion_recipe M phi upper /\sf_relation M SFAll upper (zeroM M) all1 /\sf_relation M SFAll all1 (zeroM M) out.
Definition source_kprime_core_recipe_formula (phi out:term) :form :=
  ∃∃ (source_upper_conclusion_recipe_formula (code_lift2 phi) $1 ∧
    (sf_formula SFAll $1 zero $0 ∧sf_formula SFAll $0 zero (code_lift2 out))).
Local Opaque holds numerical_renaming_formula source_emitted_closure_recipe_formula sf_formula.

Theorem source_upper_conclusion_recipe_formula_correct M rho phi out :
  holds M rho(source_upper_conclusion_recipe_formula phi out) <->
  source_upper_conclusion_recipe M (evalM M rho phi)(evalM M rho out).
Proof.
  unfold source_upper_conclusion_recipe_formula,source_upper_conclusion_recipe,source_formula_shift,source_native_k_upshift.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite source_emitted_closure_recipe_formula_correct. setoid_rewrite sf_formula_correct.
  unfold evalM,native_lift6. repeat setoid_rewrite eval_up. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Theorem source_kprime_core_recipe_formula_correct M rho phi out :
  holds M rho(source_kprime_core_recipe_formula phi out) <->
  source_kprime_core_recipe M (evalM M rho phi)(evalM M rho out).
Proof.
  unfold source_kprime_core_recipe_formula,source_kprime_core_recipe.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_upper_conclusion_recipe_formula_correct. setoid_rewrite sf_formula_correct.
  unfold evalM,code_lift2. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_upper_conclusion_recipe_total M phi :exists out,source_upper_conclusion_recipe M phi out.
Proof.
  destruct(numerical_renaming_total M phi (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(p&HP).
  destruct(source_emitted_closure_recipe_total M phi) as(h&HH).
  destruct(numerical_renaming_total M h (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1)) as(shifted&HS).
  destruct(sf_relation_total M SFMember (code_numeral M 1)(zeroM M)) as(atom&HA).
  destruct(sf_relation_total M SFImpl p atom) as(root&HR).
  destruct(sf_relation_total M SFAnd root shifted) as(body&HB).
  destruct(sf_relation_total M SFEx body (zeroM M)) as(out&HO).
  exists out,p,h,shifted,atom,root,body. repeat split;assumption.
Qed.
Theorem source_kprime_core_recipe_total M phi :exists out,source_kprime_core_recipe M phi out.
Proof.
  destruct(source_upper_conclusion_recipe_total M phi) as(u&HU).
  destruct(sf_relation_total M SFAll u (zeroM M)) as(a&HA).
  destruct(sf_relation_total M SFAll a (zeroM M)) as(out&HO).
  exists out,u,a. auto.
Qed.
Theorem source_upper_conclusion_recipe_functional M phi a b :
  source_upper_conclusion_recipe M phi a ->source_upper_conclusion_recipe M phi b ->a=b.
Proof.
  intros(p&h&s&atom&r&body&HP&HH&HS&HA&HR&HB&HO)
    (p'&h'&s'&atom'&r'&body'&HP'&HH'&HS'&HA'&HR'&HB'&HO').
  pose proof(numerical_renaming_functional M phi _ _ _ _ p p' HP HP') as EP. subst p'.
  pose proof(source_emitted_closure_recipe_functional M phi h h' HH HH') as EH. subst h'.
  pose proof(numerical_renaming_functional M h _ _ _ _ s s' HS HS') as ES. subst s'.
  pose proof(sf_relation_functional M SFMember _ _ atom atom' HA HA') as EA. subst atom'.
  pose proof(sf_relation_functional M SFImpl _ _ r r' HR HR') as ER. subst r'.
  pose proof(sf_relation_functional M SFAnd _ _ body body' HB HB') as EB. subst body'.
  exact(sf_relation_functional M SFEx _ _ a b HO HO').
Qed.
Theorem source_kprime_core_recipe_functional M phi a b :
  source_kprime_core_recipe M phi a ->source_kprime_core_recipe M phi b ->a=b.
Proof.
  intros(u&f&HU&HF&HO)(u'&f'&HU'&HF'&HO').
  pose proof(source_upper_conclusion_recipe_functional M phi u u' HU HU') as EU. subst u'.
  pose proof(sf_relation_functional M SFAll _ _ f f' HF HF') as EF. subst f'.
  exact(sf_relation_functional M SFAll _ _ a b HO HO').
Qed.

Theorem source_upper_conclusion_recipe_bound M phi out n :
  source_bounded M phi (succM M(succM M n)) ->source_upper_conclusion_recipe M phi out ->
  source_bounded M out (succM M(succM M n)).
Proof.
  intros HP(p&h&s&atom&r&body&HR&HH&HS&HA&HI&HB&HO).
  pose proof(source_shift_bound M phi p (succM M(succM M n)) HP HR) as BP.
  pose proof(source_emitted_closure_recipe_bound M phi h n HP HH) as BH.
  pose proof(source_native_k_upshift_bound M h s (succM M n) BH HS) as BS.
  apply(proj2(source_bounded_accept_unary M SFEx body out _ (or_intror eq_refl) HO)).
  apply(proj2(source_bounded_accept_binary M SFAnd r s body _ (or_introl eq_refl) HB)). split;[|exact BS].
  apply(proj2(source_bounded_accept_binary M SFImpl p atom r _ (or_intror(or_intror eq_refl)) HI)). split;[exact BP|].
  apply(proj2(source_bounded_accept_atom M SFMember _ _ atom _ (or_introl eq_refl) HA)).
  split;[apply coding_lt_succ_cancel|];apply coding_zero_lt_succ.
Qed.
Theorem source_kprime_core_recipe_bound M phi out n :
  source_bounded M phi (succM M(succM M n)) ->source_kprime_core_recipe M phi out ->source_bounded M out n.
Proof.
  intros HP(u&f&HU&HF&HO).
  apply(proj2(source_bounded_accept_unary M SFAll f out n (or_introl eq_refl) HO)).
  apply(proj2(source_bounded_accept_unary M SFAll u f _ (or_introl eq_refl) HF)).
  exact(source_upper_conclusion_recipe_bound M phi u n HP HU).
Qed.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Definition native_upper_conclusion (phi:sf_form) :sf_form :=
  ∃((phi[↑] →$1 ∈' $0) ∧(native_emitted_closure phi)[up ↑]).
Definition native_kprime_core (phi:sf_form) :sf_form :=∀∀native_upper_conclusion phi.
Theorem source_upper_conclusion_recipe_finite M (phi:sf_form) :
  source_upper_conclusion_recipe M (code_numeral M(sf_encode phi))
    (code_numeral M(sf_encode(native_upper_conclusion phi))).
Proof.
  exists (code_numeral M(sf_encode phi[↑])),(code_numeral M(sf_encode(native_emitted_closure phi))),
    (code_numeral M(sf_encode((native_emitted_closure phi)[up ↑]))),
    (code_numeral M(sf_encode($1 ∈' $0))),
    (code_numeral M(sf_encode(phi[↑]→$1 ∈' $0))),
    (code_numeral M(sf_encode((phi[↑]→$1 ∈' $0)∧(native_emitted_closure phi)[up ↑]))).
  split;[apply source_formula_numeral_shift|].
  split;[apply source_emitted_closure_recipe_finite|].
  split;[apply source_native_k_upshift_finite|].
  split;[exact(sf_make_numeral M SFMember 1 0)|].
  split;[exact(sf_make_numeral M SFImpl (sf_encode phi[↑]) (sf_encode($1 ∈' $0)))|].
  split;[exact(sf_make_numeral M SFAnd (sf_encode(phi[↑]→$1 ∈' $0)) (sf_encode((native_emitted_closure phi)[up ↑])))|].
  exact(sf_make_numeral M SFEx (sf_encode((phi[↑]→$1 ∈' $0)∧(native_emitted_closure phi)[up ↑])) 0).
Qed.
Theorem source_kprime_core_recipe_finite M (phi:sf_form) :
  source_kprime_core_recipe M (code_numeral M(sf_encode phi))(code_numeral M(sf_encode(native_kprime_core phi))).
Proof.
  exists (code_numeral M(sf_encode(native_upper_conclusion phi))),
    (code_numeral M(sf_encode(∀native_upper_conclusion phi))).
  split;[apply source_upper_conclusion_recipe_finite|].
  split;[exact(sf_make_numeral M SFAll (sf_encode(native_upper_conclusion phi)) 0)|].
  exact(sf_make_numeral M SFAll (sf_encode(∀native_upper_conclusion phi)) 0).
Qed.

Print Assumptions source_upper_conclusion_recipe_formula_correct.
Print Assumptions source_kprime_core_recipe_formula_correct.
Print Assumptions source_upper_conclusion_recipe_total.
Print Assumptions source_kprime_core_recipe_total.
Print Assumptions source_upper_conclusion_recipe_functional.
Print Assumptions source_kprime_core_recipe_functional.
Print Assumptions source_upper_conclusion_recipe_bound.
Print Assumptions source_kprime_core_recipe_bound.
Print Assumptions source_upper_conclusion_recipe_finite.
Print Assumptions source_kprime_core_recipe_finite.
