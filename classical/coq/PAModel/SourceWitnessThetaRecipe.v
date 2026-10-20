(** Literal arbitrary-code witness_theta from KUpperReflect. The two matrix
    maps are genuine packed renamings; their parameter tails are4 and5.
    This file constructs syntax, not reflection or its set-theoretic proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
  NumericalEnvironments NumericalSubstitution RenamingSubstitution SchemaRenamingDescriptors
  SourceNumeralLift SubstitutionSource SourceFiniteCutoffShift SchemaConstructorBounds.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition witness_theta_dividend (inside:bool) :=if inside then 2 else 4.
Definition witness_theta_delta (inside:bool) :=if inside then 3 else 2.
Definition witness_theta_second (inside:bool) :=if inside then 2 else 1.
Definition witness_theta_tail inside :=2+witness_theta_delta inside.
Definition witness_theta_sigma inside i :sf_term :=match i with
  0=>var 0 |1=>var(witness_theta_second inside)|S(S k)=>var(witness_theta_tail inside+k) end.
Definition source_witness_theta_matrix M inside phi out :=numerical_renaming M phi
  (code_numeral M(witness_theta_dividend inside))(code_numeral M 1)(code_numeral M 2)
  (code_numeral M(witness_theta_delta inside)) out.
Lemma witness_theta_lookup_zero M inside :renaming_lookup M
  (code_numeral M(witness_theta_dividend inside))(code_numeral M 1)(code_numeral M 2)
  (code_numeral M(witness_theta_delta inside))(zeroM M)(zeroM M).
Proof.
  apply(proj2(renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M(code_numeral M 1)))).
  destruct inside;cbn[witness_theta_dividend].
  - apply(descriptor_beta_certificate M 2 1 0 0 1);reflexivity||lia.
  - apply(descriptor_beta_certificate M 4 1 0 0 2);reflexivity||lia.
Qed.
Lemma witness_theta_lookup_one M inside :renaming_lookup M
  (code_numeral M(witness_theta_dividend inside))(code_numeral M 1)(code_numeral M 2)
  (code_numeral M(witness_theta_delta inside))(code_numeral M 1)
  (code_numeral M(witness_theta_second inside)).
Proof.
  apply(proj2(renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M(code_numeral M 1)))).
  destruct inside;cbn[witness_theta_dividend witness_theta_second].
  - apply(descriptor_beta_certificate M 2 1 1 2 0);reflexivity||lia.
  - apply(descriptor_beta_certificate M 4 1 1 1 1);reflexivity||lia.
Qed.
Lemma witness_theta_lookup_finite M inside i :renaming_lookup M
  (code_numeral M(witness_theta_dividend inside))(code_numeral M 1)(code_numeral M 2)
  (code_numeral M(witness_theta_delta inside))(code_numeral M i)
  (code_numeral M(sf_index(witness_theta_sigma inside i))).
Proof.
  destruct i as[|[|i]];[apply witness_theta_lookup_zero|apply witness_theta_lookup_one|].
  apply renaming_lookup_outside.
  - intro H. change(coding_lt M (succM M(succM M(code_numeral M i)))
      (succM M(succM M(zeroM M)))) in H.
    apply(proj1(coding_lt_succ_cancel M _ _)) in H.
    apply(proj1(coding_lt_succ_cancel M _ _)) in H. exact(coding_not_lt_zero M _ H).
  - rewrite descriptor_numeral_add. f_equal. unfold witness_theta_sigma,witness_theta_tail;cbn[sf_index]. lia.
Qed.
Theorem source_witness_theta_matrix_bound M inside phi out n :
  source_bounded M phi (succM M(succM M n)) ->source_witness_theta_matrix M inside phi out ->
  source_bounded M out (source_succ_iter M (witness_theta_tail inside) n).
Proof.
  intros HP HR. apply(numerical_renaming_preserves_bound M phi _ _ _ _ out _ _ HP HR).
  intros i j HI HJ. destruct(environment_lt_cases M i (code_numeral M 2)) as[Hin|Hout].
  - change(coding_lt M i (succM M(succM M(zeroM M)))) in Hin.
    apply coding_lt_succ_cases in Hin. destruct Hin as[Hin|E].
    + apply coding_lt_succ_cases in Hin. destruct Hin as[HBad|E].
      * exfalso. exact(coding_not_lt_zero M i HBad).
      * subst i. pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HJ(witness_theta_lookup_zero M inside)) as EJ.
        subst j. destruct inside;cbn[witness_theta_tail witness_theta_delta source_succ_iter];schema_small_index.
    + subst i. pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HJ(witness_theta_lookup_one M inside)) as EJ.
      subst j. destruct inside;cbn[witness_theta_second witness_theta_tail witness_theta_delta source_succ_iter];schema_small_index.
  - apply renaming_lookup_outside in HJ;[|exact Hout]. subst j.
    destruct inside;cbn[witness_theta_delta witness_theta_tail source_succ_iter code_numeral];
      rewrite Arithmetic.add_comm;repeat rewrite Arithmetic.add_succ;rewrite Arithmetic.add_zero;
      repeat apply(proj2(coding_lt_succ_cancel M _ _));exact HI.
Qed.
Theorem source_witness_theta_matrix_finite M inside (phi:sf_form) :
  source_witness_theta_matrix M inside (code_numeral M(sf_encode phi))
    (code_numeral M(sf_encode(phi[witness_theta_sigma inside]))).
Proof.
  apply(proj2(numerical_renaming_substitution M _ _ _ _ _ _)).
  apply(fixed_source_substitution M (fun _=>zeroM M) phi (witness_theta_sigma inside)
    (code_numeral M(witness_theta_dividend inside))(code_numeral M 1)(code_numeral M 2)
    (addM M(code_numeral M 2)(code_numeral M(witness_theta_delta inside))) _ _).
  - intro i. exact(proj1(renaming_substitution_lookup M _ _ _ _ _ _)(witness_theta_lookup_finite M inside i)).
  - exact(source_formula_numeral_graph M phi).
  - exact(source_formula_numeral_graph M phi[witness_theta_sigma inside]).
Qed.

Definition source_witness_theta_recipe M phi out :=exists a b guard negative some left right,
  source_witness_theta_matrix M false phi a /\source_witness_theta_matrix M true phi b /\
  sf_relation M SFMember (code_numeral M 2)(code_numeral M 3) guard /\
  sf_relation M SFImpl guard (zeroM M) negative /\sf_relation M SFEx b (zeroM M) some /\
  sf_relation M SFAnd guard a left /\sf_relation M SFAnd negative some right /\
  sf_relation M SFOr left right out.
Definition witness_theta_lift7(t:term):=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Definition source_witness_theta_recipe_formula(phi out:term):form :=
  ∃∃∃∃∃∃∃(numerical_renaming_formula (witness_theta_lift7 phi)(num 4)(num 1)(num 2)(num 2) $6 ∧
    (numerical_renaming_formula (witness_theta_lift7 phi)(num 2)(num 1)(num 2)(num 3) $5 ∧
    (sf_formula SFMember (num 2)(num 3) $4 ∧(sf_formula SFImpl $4 zero $3 ∧
    (sf_formula SFEx $5 zero $2 ∧(sf_formula SFAnd $4 $6 $1 ∧
    (sf_formula SFAnd $3 $2 $0 ∧sf_formula SFOr $1 $0 (witness_theta_lift7 out)))))))).
Local Opaque holds numerical_renaming_formula sf_formula.
Theorem source_witness_theta_recipe_formula_correct M rho phi out :
  holds M rho(source_witness_theta_recipe_formula phi out) <->
  source_witness_theta_recipe M (evalM M rho phi)(evalM M rho out).
Proof.
  unfold source_witness_theta_recipe_formula,source_witness_theta_recipe,source_witness_theta_matrix.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite numerical_renaming_formula_correct. setoid_rewrite sf_formula_correct.
  unfold evalM,witness_theta_lift7. repeat setoid_rewrite eval_up.
  repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Theorem source_witness_theta_recipe_total M phi :exists out,source_witness_theta_recipe M phi out.
Proof.
  destruct(numerical_renaming_total M phi (code_numeral M 4)(code_numeral M 1)(code_numeral M 2)(code_numeral M 2)) as(a&HA).
  destruct(numerical_renaming_total M phi (code_numeral M 2)(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)) as(b&HB).
  destruct(sf_relation_total M SFMember (code_numeral M 2)(code_numeral M 3)) as(guard&HG).
  destruct(sf_relation_total M SFImpl guard (zeroM M)) as(negative&HN).
  destruct(sf_relation_total M SFEx b (zeroM M)) as(some&HE).
  destruct(sf_relation_total M SFAnd guard a) as(left&HL).
  destruct(sf_relation_total M SFAnd negative some) as(right&HR).
  destruct(sf_relation_total M SFOr left right) as(out&HO).
  exists out,a,b,guard,negative,some,left,right. repeat split;assumption.
Qed.
Theorem source_witness_theta_recipe_functional M phi a b :
  source_witness_theta_recipe M phi a ->source_witness_theta_recipe M phi b ->a=b.
Proof.
  intros(x&y&g&n&e&l&r&HX&HY&HG&HN&HE&HL&HR&HO)
    (x'&y'&g'&n'&e'&l'&r'&HX'&HY'&HG'&HN'&HE'&HL'&HR'&HO').
  pose proof(numerical_renaming_functional M phi _ _ _ _ x x' HX HX') as E. subst x'.
  pose proof(numerical_renaming_functional M phi _ _ _ _ y y' HY HY') as E. subst y'.
  pose proof(sf_relation_functional M SFMember _ _ g g' HG HG') as E. subst g'.
  pose proof(sf_relation_functional M SFImpl _ _ n n' HN HN') as E. subst n'.
  pose proof(sf_relation_functional M SFEx _ _ e e' HE HE') as E. subst e'.
  pose proof(sf_relation_functional M SFAnd _ _ l l' HL HL') as E. subst l'.
  pose proof(sf_relation_functional M SFAnd _ _ r r' HR HR') as E. subst r'.
  exact(sf_relation_functional M SFOr _ _ a b HO HO').
Qed.
Theorem source_witness_theta_recipe_bound M phi out n :
  source_bounded M phi (succM M(succM M n)) ->source_witness_theta_recipe M phi out ->
  source_bounded M out (source_succ_iter M 4 n).
Proof.
  intros HP(a&b&g&negative&some&left&right&HA&HB&HG&HN&HE&HL&HR&HO).
  pose proof(source_witness_theta_matrix_bound M false phi a n HP HA) as BA.
  pose proof(source_witness_theta_matrix_bound M true phi b n HP HB) as BB.
  assert(BG:source_bounded M g (source_succ_iter M 4 n)).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ g _ (or_introl eq_refl) HG)).
    split;cbn[source_succ_iter];schema_small_index. }
  apply(proj2(source_bounded_accept_binary M SFOr left right out _ (or_intror(or_introl eq_refl)) HO)). split.
  - apply(proj2(source_bounded_accept_binary M SFAnd g a left _ (or_introl eq_refl) HL)). split;assumption.
  - apply(proj2(source_bounded_accept_binary M SFAnd negative some right _ (or_introl eq_refl) HR)). split.
    + apply(proj2(source_bounded_accept_binary M SFImpl g (zeroM M) negative _ (or_intror(or_intror eq_refl)) HN)).
      split;[exact BG|apply source_bounded_accept_falsity].
    + exact(proj2(source_bounded_accept_unary M SFEx b some _ (or_intror eq_refl) HE) BB).
Qed.

Print Assumptions source_witness_theta_matrix_finite.
Print Assumptions source_witness_theta_recipe_formula_correct.
Print Assumptions source_witness_theta_recipe_total.
Print Assumptions source_witness_theta_recipe_functional.
Print Assumptions source_witness_theta_recipe_bound.
