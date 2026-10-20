(** The three emitted-closure matrix occurrences in the canonical K
    recipe match the exact named scopes. All intermediate syntax actions
    are genuine numerical graphs on an arbitrary internally coded matrix. *)
From Stdlib Require Import List Lia.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution SourceBounded SourceRoleAbstraction SourceRoleReopening
  SourceFiniteCutoffShift SourceNativeKMatrixMaps SourceFourMapComparison
  SourceNamedScopes SourceNamedScopeBinding SourceFiniteMapLifts NamedCoreScopedRecipe.
From FOL.Tennenbaum Require Import Peano.
Import ListNotations.
Unset Implicit Arguments.

Definition native_named_leaf_depth kind :=match kind with NativeKA=>3|NativeKB=>5|NativeKC=>6 end.
Definition native_named_leaf_scope (M:Model) kind (a b c:carrier M) :=match kind with
  | NativeKA=>[a;b;c] |NativeKB=>[b;a;a;b;c] |NativeKC=>[b;b;a;a;b;c] end.
Lemma native_named_leaf_scope_length M kind a b c :
  length (native_named_leaf_scope M kind a b c)=native_named_leaf_depth kind.
Proof. destruct kind;reflexivity. Qed.

Lemma native_k_arbitrary_tail M kind i :
  renaming_lookup M (code_numeral M (native_k_dividend kind)) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M (native_k_delta kind))
    (succM M (succM M i)) (named_scope_succ M (S (native_named_leaf_depth kind)) i).
Proof.
  assert (HNot:~coding_lt M (succM M (succM M i)) (code_numeral M 2)).
  { intro H. apply (proj1 (coding_lt_succ_cancel M _ _)) in H.
    apply (proj1 (coding_lt_succ_cancel M _ _)) in H. exact (coding_not_lt_zero M i H). }
  apply (proj2 (renaming_lookup_outside M (code_numeral M (native_k_dividend kind))
    (code_numeral M 1) (code_numeral M 2) (code_numeral M (native_k_delta kind))
    (succM M (succM M i)) (named_scope_succ M (S (native_named_leaf_depth kind)) i) HNot)).
  destruct kind;cbn [native_k_delta native_named_leaf_depth named_scope_succ code_numeral];
    rewrite Arithmetic.add_comm;repeat rewrite Arithmetic.add_succ;rewrite Arithmetic.add_zero;reflexivity.
Qed.

Lemma named_scope_default_intro M names i :
  (forall x,In x names ->i<>x) ->named_scope_index M names i (named_scope_succ M (length names) i).
Proof.
  intro HN. destruct (named_scope_index_total M names i) as (v&HV).
  pose proof (named_scope_index_default M names i v HN HV) as E. now rewrite <-E.
Qed.

Theorem native_core_leaf_pointwise M kind a b c arb arc sb sc cb cc cn db dc dn i j1 j2 j3 v :
  a<>b ->c<>a ->c<>b ->coding_lt M i c ->source_role_map M a b arb arc ->
  source_cutoff_shift_map M (native_named_leaf_depth kind) cb cc cn ->
  source_substitution_lifts M (native_named_leaf_depth kind) sb sc (code_numeral M 2) (zeroM M) db dc dn ->
  renaming_lookup M arb arc (source_role_length M a b) (code_numeral M 2) i j1 ->
  renaming_lookup M (code_numeral M (native_k_dividend kind)) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M (native_k_delta kind)) j1 j2 ->
  substitution_lookup M cb cc cn (code_numeral M (S (native_named_leaf_depth kind))) j2 j3 ->
  substitution_lookup M db dc dn (code_numeral M (native_named_leaf_depth kind)) j3 v ->
  named_scope_index M (native_named_leaf_scope M kind a b c) i v.
Proof.
  intros Hab Hca Hcb HI HM HC HL HRole HK HCut HLast.
  apply HM in HRole. destruct HRole as [[-> ->]|[HNb [[-> ->]|[HNa ->]]]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j2 _ HK (native_k_lookup_first M kind)) as E2. subst j2.
    pose proof (source_cutoff_shift_head M (native_named_leaf_depth kind) cb cc cn
      (native_k_first kind) ltac:(destruct kind;cbn;lia) HC) as HCut'.
    pose proof (substitution_lookup_functional M _ _ _ _ _ j3 _ HCut HCut') as E3. subst j3.
    pose proof (source_substitution_lifts_head M (native_named_leaf_depth kind) sb sc (code_numeral M 2)
      (zeroM M) db dc dn (native_k_first kind) ltac:(destruct kind;cbn;lia) HL) as HLast'.
    rewrite named_scope_succ_zero in HLast'.
    pose proof (substitution_lookup_functional M _ _ _ _ _ v _ HLast HLast') as EV. subst v.
    destruct kind;cbn [native_named_leaf_scope native_k_first named_scope_index];named_scope_atom_index.
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j2 _ HK (native_k_lookup_second M kind)) as E2. subst j2.
    pose proof (source_cutoff_shift_head M (native_named_leaf_depth kind) cb cc cn
      (native_k_second kind) ltac:(destruct kind;cbn;lia) HC) as HCut'.
    pose proof (substitution_lookup_functional M _ _ _ _ _ j3 _ HCut HCut') as E3. subst j3.
    pose proof (source_substitution_lifts_head M (native_named_leaf_depth kind) sb sc (code_numeral M 2)
      (zeroM M) db dc dn (native_k_second kind) ltac:(destruct kind;cbn;lia) HL) as HLast'.
    rewrite named_scope_succ_zero in HLast'.
    pose proof (substitution_lookup_functional M _ _ _ _ _ v _ HLast HLast') as EV. subst v.
    destruct kind;cbn [native_named_leaf_scope native_k_second named_scope_index];named_scope_atom_index.
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j2 _ HK (native_k_arbitrary_tail M kind i)) as E2. subst j2.
    pose proof (source_cutoff_shift_tail M (native_named_leaf_depth kind) cb cc cn (succM M i) HC) as HCut'.
    rewrite !named_scope_succ_succ in HCut'.
    pose proof (substitution_lookup_functional M _ _ _ _ _ j3 _ HCut HCut') as E3. subst j3.
    pose proof (source_substitution_lifts_tail M (native_named_leaf_depth kind) sb sc (code_numeral M 2)
      (zeroM M) db dc dn (succM M (succM M i)) i HL (source_role_reopening_tail M sb sc i)) as HLast'.
    rewrite named_scope_succ_zero,!named_scope_succ_succ in HLast'.
    pose proof (substitution_lookup_functional M _ _ _ _ _ v _ HLast HLast') as EV. subst v.
    rewrite <- (native_named_leaf_scope_length M kind a b c).
    apply named_scope_default_intro. intros x HX.
    assert (HIc:i<>c).
    { exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) i c HI). }
    destruct kind;cbn [native_named_leaf_scope In] in HX;intuition congruence.
Qed.

Theorem native_core_leaf_alignment M kind a b c phi abstract matrix shifted out arb arc sb sc cb cc cn db dc dn :
  a<>b ->c<>a ->c<>b ->source_bounded M phi c ->source_role_map M a b arb arc ->
  numerical_renaming M phi arb arc (source_role_length M a b) (code_numeral M 2) abstract ->
  source_native_k_matrix M kind abstract matrix ->
  source_cutoff_shift_map M (native_named_leaf_depth kind) cb cc cn ->
  numerical_substitution M matrix cb cc cn (code_numeral M (S (native_named_leaf_depth kind))) shifted ->
  source_substitution_lifts M (native_named_leaf_depth kind) sb sc (code_numeral M 2) (zeroM M) db dc dn ->
  numerical_substitution M shifted db dc dn (code_numeral M (native_named_leaf_depth kind)) out ->
  named_scope_renaming M (native_named_leaf_scope M kind a b c) phi out.
Proof.
  intros Hab Hca Hcb HB HM HR HK HC HS HL HLast.
  destruct (named_scope_map_total M (native_named_leaf_scope M kind a b c)) as (tb&tc&HT).
  exists tb,tc. split;[exact HT|]. apply (proj2 (numerical_renaming_substitution M phi tb tc
    (named_scope_bound M (native_named_leaf_scope M kind a b c))
    (code_numeral M (length (native_named_leaf_scope M kind a b c))) out)).
  apply (numerical_two_renamings_two_substitutions_compare M phi c
    arb arc (source_role_length M a b) (code_numeral M 2)
    (code_numeral M (native_k_dividend kind))(code_numeral M 1)(code_numeral M 2)(code_numeral M (native_k_delta kind))
    cb cc cn (code_numeral M (S (native_named_leaf_depth kind)))
    db dc dn (code_numeral M (native_named_leaf_depth kind))
    tb tc (named_scope_bound M (native_named_leaf_scope M kind a b c))
    (addM M (named_scope_bound M (native_named_leaf_scope M kind a b c))
      (code_numeral M (length (native_named_leaf_scope M kind a b c)))) abstract matrix shifted out
    HB HR HK HS HLast).
  intros i j1 j2 j3 v HI H1 H2 H3 H4.
  apply (proj1 (renaming_substitution_lookup M tb tc _ _ i v)). apply HT.
  exact (native_core_leaf_pointwise M kind a b c arb arc sb sc cb cc cn db dc dn i j1 j2 j3 v
    Hab Hca Hcb HI HM HC HL H1 H2 H3 H4).
Qed.

Print Assumptions native_core_leaf_alignment.
