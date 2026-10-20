(** The repeated-active-name closure follows from one selected member.
    This is a pure source deduction for an arbitrary internally coded
    matrix, before Empty or Hosting is used to choose the outer carrier. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments SourceSequents NumericalSourceFull
  SourceInstantiationConstructors SourceUniversalDistribution NativeKBundle NativeNamedRegularity
  SourceNamedVacuity SourceNamedQuantifierRules NativeNamedProofRules.
Unset Implicit Arguments.

Definition NNT_equal_witness name container matrix :=
  NNTEx name (NNTAnd matrix (NNTAtom false name container)).
Definition NNT_equal_rest name container matrix :=
  NNTAll name (NNTImpl (NNT_subset name name container)
    (NNTAll name (NNTImpl matrix (NNT_equal_witness name container matrix)))).
Definition NNT_equal_closure name container matrix :=
  NNTAll name (NNTImpl (NNTAtom false name container)
    (NNTEx name (NNTAnd matrix (NNT_equal_rest name container matrix)))).

Theorem native_equal_closure_from_witness M env name container matrix x witness closure imp :
  code_relation M env name x ->
  native_named_evaluation M env (NNT_equal_witness name container matrix) witness ->
  native_named_evaluation M env (NNT_equal_closure name container matrix) closure ->
  sf_relation M SFImpl witness closure imp ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) imp.
Proof.
  intros HX HW HC HI.
  destruct (native_named_evaluation_bounded M env (NNT_equal_witness name container matrix) witness HW)
    as(k&HBW).
  destruct (native_named_quantifier_view M env false name
    (NNTAnd matrix (NNTAtom false name container)) witness HW) as(y&body&HY&HBody&HQuant).
  rewrite (code_relation_functional M name env y x HY HX) in HQuant.
  destruct (native_named_evaluation_bounded M env (NNTAnd matrix (NNTAtom false name container))
    body HBody) as(l&HBBody).
  pose proof (source_named_quantifier_is_vacuous M false x body witness l HBBody HQuant) as HVac.
  destruct (environment_cons_total M (zeroM M)(zeroM M)(zeroM M) witness) as(b&c&n&HCons).
  assert (HCtx:context_bounded M b c n k).
  { apply (proj2 (context_bounded_cons M (zeroM M)(zeroM M)(zeroM M) witness b c n k HCons)).
    split;[exact HBW|apply context_bounded_empty]. }
  assert (HMember:context_member M b c n witness).
  { apply (proj2 (context_member_cons M (zeroM M)(zeroM M)(zeroM M) witness b c n witness HCons)). now left. }
  assert (P:source_full_prv M b c n witness).
  { apply full_source_Ctx;[exists k;auto|exact HMember]. }
  assert (HContextVacuous:source_named_context_vacuous M b c n x).
  { intros f HF. apply (proj1 (context_member_cons M (zeroM M)(zeroM M)(zeroM M)
      witness b c n f HCons)) in HF. destruct HF as[->|HF];[exact HVac|].
    exfalso. exact (context_empty M (zeroM M)(zeroM M) f HF). }
  assert (PW:native_source_proof M b c n env (NNT_equal_witness name container matrix)).
  { intros out HO. rewrite (native_named_evaluation_unique M env _ out witness HO HW). exact P. }
  assert (PRequest:native_source_proof M b c n env
    (NNTAll name (NNTImpl matrix (NNT_equal_witness name container matrix)))).
  { apply (native_source_all_intro M b c n env x name _ HX HContextVacuous).
    exact (native_source_ignore M b c n env matrix _ PW). }
  assert (PRest:native_source_proof M b c n env (NNT_equal_rest name container matrix)).
  { apply (native_source_all_intro M b c n env x name _ HX HContextVacuous).
    exact (native_source_ignore M b c n env (NNT_subset name name container) _ PRequest). }
  assert (PInner:native_source_proof M b c n env
    (NNTEx name (NNTAnd matrix (NNT_equal_rest name container matrix)))).
  { apply (native_source_exists_map M b c n env x name
      (NNTAnd matrix (NNTAtom false name container))
      (NNTAnd matrix (NNT_equal_rest name container matrix)) HX HContextVacuous);[|exact PW].
    exact (native_source_conjunct_replace M b c n env matrix
      (NNTAtom false name container)(NNT_equal_rest name container matrix) PRest). }
  assert (PClosure:source_full_prv M b c n closure).
  { exact ((native_source_all_intro M b c n env x name
      (NNTImpl (NNTAtom false name container)
        (NNTEx name (NNTAnd matrix (NNT_equal_rest name container matrix)))) HX HContextVacuous
      (native_source_ignore M b c n env (NNTAtom false name container) _ PInner)) closure HC). }
  apply (full_source_II M (zeroM M)(zeroM M)(zeroM M) witness closure imp b c n);
    [|exact PClosure|exact HCons|exact HI].
  destruct (source_binary_bound_exists M SFImpl witness closure imp
    (or_intror(or_intror eq_refl)) HI
    (ex_intro _ k HBW) (native_named_evaluation_bounded M env _ closure HC)) as(bound&HBound).
  exists bound. split;[exact HBound|apply context_bounded_empty].
Qed.

Print Assumptions native_equal_closure_from_witness.
