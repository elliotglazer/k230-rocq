(** The three literal matrix renamings in KPrimeCore.emitted_closure.
    Their beta tables act on arbitrary internal source formula codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
  NumericalSubstitution RenamingSubstitution SchemaRenamingDescriptors NumericalEnvironments
  SourceNumeralLift SubstitutionSource SourceFiniteCutoffShift SchemaConstructorBounds.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Inductive native_k_matrix_kind := NativeKA | NativeKB | NativeKC.
Definition native_k_dividend s := match s with NativeKA=>3|NativeKB=>4|NativeKC=>2 end.
Definition native_k_delta s := match s with NativeKA=>2|NativeKB=>4|NativeKC=>5 end.
Definition native_k_first s := match s with NativeKA=>1|_=>0 end.
Definition native_k_second s := match s with NativeKA=>0|NativeKB=>1|NativeKC=>2 end.
Definition native_k_tail s := 2+native_k_delta s.
Definition native_k_sigma s (i:nat) :sf_term :=
  match i with 0=>var(native_k_first s)|1=>var(native_k_second s)|S(S k)=>var(native_k_tail s+k) end.
Definition source_native_k_matrix M s phi out :=
  numerical_renaming M phi (code_numeral M (native_k_dividend s)) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M (native_k_delta s)) out.

Lemma native_k_lookup_first M s :
  renaming_lookup M (code_numeral M (native_k_dividend s)) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M (native_k_delta s)) (zeroM M) (code_numeral M(native_k_first s)).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1)))).
  destruct s;cbn [native_k_dividend native_k_first].
  - apply (descriptor_beta_certificate M 3 1 0 1 1);reflexivity||lia.
  - apply (descriptor_beta_certificate M 4 1 0 0 2);reflexivity||lia.
  - apply (descriptor_beta_certificate M 2 1 0 0 1);reflexivity||lia.
Qed.
Lemma native_k_lookup_second M s :
  renaming_lookup M (code_numeral M(native_k_dividend s)) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M(native_k_delta s)) (code_numeral M 1) (code_numeral M(native_k_second s)).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 1)))).
  destruct s;cbn [native_k_dividend native_k_second].
  - apply (descriptor_beta_certificate M 3 1 1 0 1);reflexivity||lia.
  - apply (descriptor_beta_certificate M 4 1 1 1 1);reflexivity||lia.
  - apply (descriptor_beta_certificate M 2 1 1 2 0);reflexivity||lia.
Qed.

Theorem native_k_fixed_lookup M s i :
  renaming_lookup M (code_numeral M(native_k_dividend s)) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M(native_k_delta s))
    (code_numeral M i) (code_numeral M(sf_index(native_k_sigma s i))).
Proof.
  destruct i as [|[|i]];[exact(native_k_lookup_first M s)|exact(native_k_lookup_second M s)|].
  apply renaming_lookup_outside.
  - intro H. change (coding_lt M (succM M(succM M(code_numeral M i)))
      (succM M(succM M(zeroM M)))) in H.
    apply (proj1(coding_lt_succ_cancel M _ _)) in H.
    apply (proj1(coding_lt_succ_cancel M _ _)) in H.
    exact(coding_not_lt_zero M _ H).
  - rewrite descriptor_numeral_add. f_equal. unfold native_k_sigma,native_k_tail;cbn [sf_index]. lia.
Qed.

Theorem source_native_k_matrix_total M s phi :exists out,source_native_k_matrix M s phi out.
Proof. apply numerical_renaming_total. Qed.
Theorem source_native_k_matrix_functional M s phi a b :
  source_native_k_matrix M s phi a ->source_native_k_matrix M s phi b ->a=b.
Proof. apply numerical_renaming_functional. Qed.

Theorem source_native_k_matrix_bound M s phi out n :
  source_bounded M phi (succM M(succM M n)) ->source_native_k_matrix M s phi out ->
  source_bounded M out (source_succ_iter M (native_k_tail s) n).
Proof.
  intros HP HR. apply (numerical_renaming_preserves_bound M phi _ _ _ _ out _ _ HP HR).
  intros i j HI HJ.
  destruct (environment_lt_cases M i (code_numeral M 2)) as [Hin|Hout].
  - change (coding_lt M i (succM M(succM M(zeroM M)))) in Hin.
    apply coding_lt_succ_cases in Hin. destruct Hin as [Hin|E].
    + apply coding_lt_succ_cases in Hin. destruct Hin as [Hbad|E].
      * exfalso. exact(coding_not_lt_zero M i Hbad).
      * subst i. pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ (native_k_lookup_first M s)) as EJ.
        subst j. destruct s;cbn[native_k_first native_k_tail native_k_delta source_succ_iter];schema_small_index.
    + subst i. pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ (native_k_lookup_second M s)) as EJ.
      subst j. destruct s;cbn[native_k_second native_k_tail native_k_delta source_succ_iter];schema_small_index.
  - apply renaming_lookup_outside in HJ;[|exact Hout]. subst j.
    destruct s;cbn[native_k_delta native_k_tail source_succ_iter code_numeral];
      rewrite Arithmetic.add_comm;repeat rewrite Arithmetic.add_succ;rewrite Arithmetic.add_zero;
      repeat apply (proj2(coding_lt_succ_cancel M _ _));exact HI.
Qed.

Theorem source_native_k_matrix_finite M s (phi:sf_form) :
  source_native_k_matrix M s (code_numeral M(sf_encode phi))
    (code_numeral M(sf_encode(phi[native_k_sigma s]))).
Proof.
  apply (proj2(numerical_renaming_substitution M _ _ _ _ _ _)).
  apply (fixed_source_substitution M (fun _=>zeroM M) phi (native_k_sigma s)
    (code_numeral M(native_k_dividend s)) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) (code_numeral M(native_k_delta s))) _ _).
  - intro i. exact(proj1(renaming_substitution_lookup M _ _ _ _ _ _)(native_k_fixed_lookup M s i)).
  - exact(source_formula_numeral_graph M phi).
  - exact(source_formula_numeral_graph M phi[native_k_sigma s]).
Qed.

Print Assumptions native_k_fixed_lookup.
Print Assumptions source_native_k_matrix_total.
Print Assumptions source_native_k_matrix_functional.
Print Assumptions source_native_k_matrix_bound.
Print Assumptions source_native_k_matrix_finite.
