(** The literal trace profile of KUpperCore at canonical free roles
    C=0, B=1 and parameters=2+k. The matrix is an arbitrary internal code. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceUpperTraceRecipe SourceFiniteCutoffShift SourceNativeKMatrixMaps
  SourcePropositionalTemplates SourceSeparationSubset SourceSeparationZeroSpecialization
  SourceNumeralLift SubstitutionSource SchemaConstructorBounds SetSchemaConstructors.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures Sets.minZF.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition E_upper_trace_profile shifted :=
  E_sf_all (E_sf_iff (E_sf_mem 0 1) (E_sf SFAnd (E_sf_mem 0 2) shifted)).
Definition source_upper_trace_profile M phi profile := exists trace shifted,
  source_upper_trace M phi trace /\ source_cutoff_shift M 1 trace shifted /\
  code_relation M (fun _=>shifted) (E_upper_trace_profile (CEvar 0)) profile.
Definition source_upper_trace_profile_formula (phi profile:term) :form :=
  ∃∃ (source_upper_trace_formula (code_lift2 phi) $1 ∧
    (source_cutoff_shift_formula 1 $1 $0 ∧
    code_formula (E_upper_trace_profile (CEvar 0))
      (fun _=>$0) (code_lift2 profile))).

Local Opaque holds source_upper_trace_formula source_cutoff_shift_formula code_formula.

Theorem source_upper_trace_profile_formula_correct M rho phi profile :
  holds M rho (source_upper_trace_profile_formula phi profile) <->
  source_upper_trace_profile M (evalM M rho phi) (evalM M rho profile).
Proof.
  unfold source_upper_trace_profile_formula,source_upper_trace_profile.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_upper_trace_formula_correct.
  setoid_rewrite source_cutoff_shift_formula_correct.
  setoid_rewrite code_formula_correct.
  unfold evalM,code_lift2. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_upper_trace_profile_total M phi :
  exists profile,source_upper_trace_profile M phi profile.
Proof.
  destruct (source_upper_trace_total M phi) as [trace HT].
  destruct (source_cutoff_shift_total M 1 trace) as [shifted HS].
  destruct (code_relation_total M (E_upper_trace_profile (CEvar 0)) (fun _=>shifted))
    as [profile HP].
  exists profile,trace,shifted. auto.
Qed.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Definition native_upper_trace_profile (phi:sf_form) :sf_form :=
  ∀ ($0 ∈' $1 ↔ ($0 ∈' $2 ∧
      ∃ ($0 ∈' $3 ∧ phi[native_k_sigma NativeKA]))).

Lemma upper_trace_shift_one (phi:sf_form) :
  (upper_trace_source phi)[source_shift_sigma 1] =
  ∃ ($0 ∈' $3 ∧ phi[native_k_sigma NativeKA]).
Proof.
  unfold upper_trace_source. cbn. f_equal. f_equal.
  rewrite subst_comp. apply subst_ext. intros [|[|i]];reflexivity.
Qed.

Theorem source_upper_trace_profile_finite M (phi:sf_form) :
  source_upper_trace_profile M (code_numeral M (sf_encode phi))
    (code_numeral M (sf_encode (native_upper_trace_profile phi))).
Proof.
  exists (code_numeral M (sf_encode (upper_trace_source phi))),
    (code_numeral M (sf_encode ((upper_trace_source phi)[source_shift_sigma 1]))).
  split;[exact(source_upper_trace_finite_lift M phi)|]. split.
  - exact (source_cutoff_shift_fixed_source M 1 (fun _=>zeroM M)
      (upper_trace_source phi) _ _ (source_formula_numeral_graph M _)
      (source_formula_numeral_graph M _)).
  - rewrite upper_trace_shift_one.
    assert (E:sf_encode (native_upper_trace_profile phi) =
      code_value (fun _=>sf_encode (∃($0 ∈' $3 ∧ phi[native_k_sigma NativeKA])))
        (E_upper_trace_profile (CEvar 0))).
    { unfold E_upper_trace_profile,native_upper_trace_profile,E_sf_all,E_sf_iff,E_sf_mem.
      repeat rewrite sf_make_value. reflexivity. }
    rewrite E. exact (code_relation_numeral M _ _).
Qed.

Print Assumptions source_upper_trace_profile_formula_correct.
Print Assumptions source_upper_trace_profile_total.
Print Assumptions source_upper_trace_profile_finite.
