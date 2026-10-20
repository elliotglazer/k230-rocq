(** Literal finite syntax of KPrimeCore.emitted_closure, with three genuine
    arithmetic renamings of an arbitrary internal formula hole. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
  NumericalRenaming SourceFiniteCutoffShift SourceNumeralLift SourceNativeKMatrixMaps.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Sets.minZF.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition E_native_subset02 :=E_sf_all(E_sf SFImpl (E_sf_mem 0 1) (E_sf_mem 0 3)).
Definition E_source_emitted_closure a b c :=
  E_sf_all(E_sf SFImpl (E_sf_mem 0 1)
    (E_sf_ex(E_sf SFAnd a
      (E_sf_all(E_sf SFImpl E_native_subset02
        (E_sf_all(E_sf SFImpl b (E_sf_ex(E_sf SFAnd c (E_sf_mem 0 5)))))))))).
Definition source_emitted_closure_recipe M phi out :=exists a b c,
  source_native_k_matrix M NativeKA phi a /\source_native_k_matrix M NativeKB phi b /\
  source_native_k_matrix M NativeKC phi c /\
  code_relation M (schema_env3 a b c) (E_source_emitted_closure (CEvar 0) (CEvar 1) (CEvar 2)) out.
Definition native_k_matrix_formula s (phi out:term) :form :=
  numerical_renaming_formula phi (num(native_k_dividend s)) (num 1) (num 2) (num(native_k_delta s)) out.
Definition source_emitted_closure_recipe_formula (phi out:term) :form :=
  ∃∃∃ (native_k_matrix_formula NativeKA (lift3 phi) $2 ∧
    (native_k_matrix_formula NativeKB (lift3 phi) $1 ∧
    (native_k_matrix_formula NativeKC (lift3 phi) $0 ∧
      code_formula (E_source_emitted_closure (CEvar 0) (CEvar 1) (CEvar 2))
        (schema_env3 $2 $1 $0) (lift3 out)))).
Local Opaque holds numerical_renaming_formula.

Theorem native_k_matrix_formula_correct M s rho phi out :
  holds M rho (native_k_matrix_formula s phi out) <->source_native_k_matrix M s (evalM M rho phi) (evalM M rho out).
Proof.
  unfold native_k_matrix_formula,source_native_k_matrix.
  rewrite numerical_renaming_formula_correct. now repeat rewrite code_eval_num.
Qed.
Theorem source_emitted_closure_recipe_formula_correct M rho phi out :
  holds M rho (source_emitted_closure_recipe_formula phi out) <->
  source_emitted_closure_recipe M (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_emitted_closure_recipe_formula,source_emitted_closure_recipe.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite native_k_matrix_formula_correct. setoid_rewrite code_formula_correct.
  unfold evalM,lift3. repeat setoid_rewrite eval_up.
  split;intros(a&b&c&HA&HB&HC&HO);exists a,b,c;repeat split;try assumption.
Qed.

Theorem source_emitted_closure_recipe_total M phi :exists out,source_emitted_closure_recipe M phi out.
Proof.
  destruct(source_native_k_matrix_total M NativeKA phi) as(a&HA).
  destruct(source_native_k_matrix_total M NativeKB phi) as(b&HB).
  destruct(source_native_k_matrix_total M NativeKC phi) as(c&HC).
  destruct(code_relation_total M (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2)) (schema_env3 a b c)) as(out&HO).
  exists out,a,b,c. auto.
Qed.
Theorem source_emitted_closure_recipe_functional M phi a b :
  source_emitted_closure_recipe M phi a ->source_emitted_closure_recipe M phi b ->a=b.
Proof.
  intros(a0&a1&a2&HA0&HA1&HA2&HA)(b0&b1&b2&HB0&HB1&HB2&HB).
  pose proof(source_native_k_matrix_functional M NativeKA phi a0 b0 HA0 HB0) as E0.
  pose proof(source_native_k_matrix_functional M NativeKB phi a1 b1 HA1 HB1) as E1.
  pose proof(source_native_k_matrix_functional M NativeKC phi a2 b2 HA2 HB2) as E2.
  subst b0 b1 b2. exact(code_relation_functional M _ _ a b HA HB).
Qed.
Theorem source_emitted_closure_recipe_bound M phi out n :
  source_bounded M phi (succM M(succM M n)) ->source_emitted_closure_recipe M phi out ->
  source_bounded M out (succM M(succM M n)).
Proof.
  intros HP(a&b&c&HA&HB&HC&HO).
  pose proof(source_native_k_matrix_bound M NativeKA phi a n HP HA) as BA.
  pose proof(source_native_k_matrix_bound M NativeKB phi b n HP HB) as BB.
  pose proof(source_native_k_matrix_bound M NativeKC phi c n HP HC) as BC.
  cbn[native_k_tail native_k_delta source_succ_iter] in BA,BB,BC.
  assert(B:schema_expression_bound M (schema_env3 a b c)
    (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2)) (succM M(succM M n))).
  { unfold E_source_emitted_closure,E_native_subset02,E_sf_all,E_sf_ex,E_sf_mem.
    repeat schema_constructor_bound;try schema_small_index;assumption. }
  exact(B out HO).
Qed.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Definition native_emitted_closure (phi:sf_form) :sf_form :=
  ∀ ($0 ∈' $1 → ∃ (phi[native_k_sigma NativeKA] ∧
    ∀ ((∀($0 ∈' $1 → $0 ∈' $3)) →
      ∀ (phi[native_k_sigma NativeKB] →∃(phi[native_k_sigma NativeKC] ∧$0 ∈' $5))))).

Lemma native_emitted_closure_code phi :
  sf_encode(native_emitted_closure phi)=
  code_value (schema_env3 (sf_encode(phi[native_k_sigma NativeKA]))
    (sf_encode(phi[native_k_sigma NativeKB])) (sf_encode(phi[native_k_sigma NativeKC])))
    (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2)).
Proof.
  unfold native_emitted_closure,E_source_emitted_closure,E_native_subset02,E_sf_all,E_sf_ex,E_sf_mem.
  repeat rewrite sf_make_value. reflexivity.
Qed.
Theorem source_emitted_closure_recipe_finite M (phi:sf_form) :
  source_emitted_closure_recipe M (code_numeral M(sf_encode phi))
    (code_numeral M(sf_encode(native_emitted_closure phi))).
Proof.
  exists (code_numeral M(sf_encode(phi[native_k_sigma NativeKA]))),
    (code_numeral M(sf_encode(phi[native_k_sigma NativeKB]))),
    (code_numeral M(sf_encode(phi[native_k_sigma NativeKC]))).
  split;[apply source_native_k_matrix_finite|].
  split;[apply source_native_k_matrix_finite|].
  split;[apply source_native_k_matrix_finite|]. rewrite native_emitted_closure_code.
  pose proof (code_relation_numeral M
    (schema_env3 (sf_encode(phi[native_k_sigma NativeKA]))
      (sf_encode(phi[native_k_sigma NativeKB])) (sf_encode(phi[native_k_sigma NativeKC])))
    (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2))) as H.
  apply (proj1(code_relation_ext M _ _ _ _ ltac:(intros [|[|i]];reflexivity))) in H.
  exact H.
Qed.

Print Assumptions source_emitted_closure_recipe_formula_correct.
Print Assumptions source_emitted_closure_recipe_total.
Print Assumptions source_emitted_closure_recipe_functional.
Print Assumptions source_emitted_closure_recipe_bound.
Print Assumptions source_emitted_closure_recipe_finite.
