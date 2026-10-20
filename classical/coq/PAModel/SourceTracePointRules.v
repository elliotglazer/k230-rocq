(** Source proof macros for KUpperCore.trace_parent and trace_member.
    The numerical instantiation graphs are actual syntax operations, with
    arbitrary internal matrices and variable names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded NumericalContexts NumericalInstantiation
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource SourceInstantiationConstructors
  SourcePropositionalTemplates SourcePropositionalSubstitution SourcePropositionalRebase
  SourceSeparationSubset SourceWFSeparationWitness SourceWFSeparationConstructor
  SourceSeparationZeroSpecialization SourceUpperTraceProfile SchemaConstructorBounds
  SetSchemaConstructors NumericalSourceFull SourceSequents SourceConjunctionRules
  SourceDerivedRules SourceNumeralLift.
Unset Implicit Arguments.

Theorem source_prop_expression_instantiation M rho rho' t a f g :
  (forall i,numerical_instantiation M (rho i) t (rho' i)) ->
  code_relation M rho (source_prop_expression a) f ->
  code_relation M rho' (source_prop_expression a) g -> numerical_instantiation M f t g.
Proof.
  intros HH HF HG. destruct (substitution_singleton_total M t) as [b [c [HB _]]].
  exists b,c. split;[exact HB|].
  apply (source_prop_expression_substitution M rho rho' b c
    (succM M (zeroM M)) (zeroM M) a);[|exact HF|exact HG].
  intro i. destruct (HH i) as [d [e [HD HS]]].
  exact (proj1 (numerical_substitution_extensional M (rho i) d e
    (succM M (zeroM M)) b c (succM M (zeroM M)) (zeroM M) (rho' i)
    (substitution_singletons_equivalent M d e b c t HD HB)) HS).
Qed.

Theorem source_instantiation_head_member M i atom x result :
  sf_relation M SFMember (zeroM M) (succM M i) atom ->
  sf_relation M SFMember x i result -> numerical_instantiation M atom x result.
Proof.
  intros HA HR. destruct (substitution_singleton_total M x) as [b [c [HB _]]].
  exists b,c. split;[exact HB|].
  apply (proj2 (numerical_substitution_member M (zeroM M) (succM M i) atom
    b c (succM M (zeroM M)) (zeroM M) result HA)).
  exists x,i. split;[exact HB|]. split;[apply substitution_singleton_tail|exact HR].
Qed.

Lemma source_trace_point_unpack M left right some point :
  code_relation M (schema_env3 left right some)
    (source_prop_expression separation_point_template) point ->
  exists rhs forward reverse,
    sf_relation M SFAnd right some rhs /\
    sf_relation M SFImpl left rhs forward /\
    sf_relation M SFImpl rhs left reverse /\
    sf_relation M SFAnd forward reverse point.
Proof.
  intro HP. destruct (sf_relation_total M SFAnd right some) as [rhs HR].
  destruct (sf_relation_total M SFImpl left rhs) as [forward HF].
  destruct (sf_relation_total M SFImpl rhs left) as [reverse HV].
  exists rhs,forward,reverse. split;[exact HR|]. split;[exact HF|]. split;[exact HV|].
  assert (HRight:code_relation M (schema_env3 left right some)
    (source_prop_expression (SPTAnd (SPTSlot 1) (SPTSlot 2))) rhs).
  { exact (source_prop_template_join M _ SFAnd (SPTSlot 1) (SPTSlot 2)
      right some rhs eq_refl eq_refl HR). }
  assert (HFwd:code_relation M (schema_env3 left right some)
    (source_prop_expression (SPTImpl (SPTSlot 0) (SPTAnd (SPTSlot 1) (SPTSlot 2)))) forward).
  { exact (source_prop_template_join M _ SFImpl (SPTSlot 0)
      (SPTAnd (SPTSlot 1) (SPTSlot 2)) left rhs forward eq_refl HRight HF). }
  assert (HRev:code_relation M (schema_env3 left right some)
    (source_prop_expression (SPTImpl (SPTAnd (SPTSlot 1) (SPTSlot 2)) (SPTSlot 0))) reverse).
  { exact (source_prop_template_join M _ SFImpl (SPTAnd (SPTSlot 1) (SPTSlot 2))
      (SPTSlot 0) rhs left reverse HRight eq_refl HV). }
  exact (proj1 (schema_expression_graph M _ SFAnd _ _ forward reverse point HFwd HRev) HP).
Qed.

Theorem source_full_trace_profile_point M cb cc cn theta profile x left right some point :
  code_relation M (fun _=>theta) (E_upper_trace_profile (CEvar 0)) profile ->
  sf_relation M SFMember x (zeroM M) left ->
  sf_relation M SFMember x (code_numeral M 1) right ->
  numerical_instantiation M theta x some ->
  code_relation M (schema_env3 left right some)
    (source_prop_expression separation_point_template) point ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn point.
Proof.
  intros HProfile HL HR HS HPoint PP.
  destruct (schema_expression_quantifier_split M (fun _=>theta) SFAll
    (E_sf_iff (E_sf_mem 0 1) (E_sf SFAnd (E_sf_mem 0 2) (CEvar 0))) profile HProfile)
    as [body [HBody HAll]].
  apply (proj1 (source_sep_point_graph M (fun _=>theta) 0 theta body eq_refl)) in HBody.
  assert (HI:numerical_instantiation M body x point).
  { apply (source_prop_expression_instantiation M
      (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
      (schema_env3 left right some) x separation_point_template body point);[|exact HBody|exact HPoint].
    intros [|[|i]];cbn [schema_env3].
    - exact (source_instantiation_head_member M (zeroM M) (source_sep_left_code M) x left
        (sf_make_numeral M SFMember 0 1) HL).
    - exact (source_instantiation_head_member M (code_numeral M 1) (source_sep_right_code M) x right
        (sf_make_numeral M SFMember 0 2) HR).
    - exact HS. }
  apply (full_source_AllE M cb cc cn body profile x point).
  - exact (source_wf_quantifier_instance M cb cc cn SFAll body profile x point
      (or_introl eq_refl) HAll (source_full_prv_wellformed M cb cc cn profile PP) HI).
  - exact PP.
  - exact HAll.
  - exact HI.
Qed.

Theorem source_full_trace_parent M cb cc cn theta profile x left right :
  code_relation M (fun _=>theta) (E_upper_trace_profile (CEvar 0)) profile ->
  sf_relation M SFMember x (zeroM M) left ->
  sf_relation M SFMember x (code_numeral M 1) right ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn left ->
  source_full_prv M cb cc cn right.
Proof.
  intros HProfile HL HR PP PL.
  destruct (numerical_instantiation_total M theta x) as [some HS].
  destruct (code_relation_total M (source_prop_expression separation_point_template)
    (schema_env3 left right some)) as [point HPoint].
  pose proof (source_full_trace_profile_point M cb cc cn theta profile x left right some point
    HProfile HL HR HS HPoint PP) as PPoint.
  destruct (source_trace_point_unpack M left right some point HPoint)
    as [rhs [forward [reverse [HAnd [HF [HV HI]]]]]].
  pose proof (source_full_conjunction_left M cb cc cn forward reverse point HI PPoint) as PF.
  pose proof (source_full_modus_ponens M cb cc cn left rhs forward HF PF PL) as PRhs.
  exact (source_full_conjunction_left M cb cc cn right some rhs HAnd PRhs).
Qed.

Theorem source_full_trace_member M cb cc cn theta profile x p left right some
    inner witness pb phixp :
  code_relation M (fun _=>theta) (E_upper_trace_profile (CEvar 0)) profile ->
  sf_relation M SFMember x (zeroM M) left ->
  sf_relation M SFMember x (code_numeral M 1) right ->
  numerical_instantiation M theta x some -> sf_relation M SFEx inner (zeroM M) some ->
  numerical_instantiation M inner p witness -> sf_relation M SFAnd pb phixp witness ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn right ->
  source_full_prv M cb cc cn pb -> source_full_prv M cb cc cn phixp ->
  source_full_prv M cb cc cn left.
Proof.
  intros HProfile HL HR HS HEx HInst HPair PP PR PPb PPhi.
  destruct (code_relation_total M (source_prop_expression separation_point_template)
    (schema_env3 left right some)) as [point HPoint].
  pose proof (source_full_trace_profile_point M cb cc cn theta profile x left right some point
    HProfile HL HR HS HPoint PP) as PPoint.
  destruct (source_trace_point_unpack M left right some point HPoint)
    as [rhs [forward [reverse [HAnd [HF [HV HI]]]]]].
  pose proof (source_full_conjunction_right M cb cc cn forward reverse point HI PPoint) as PV.
  assert (WSome:source_sequent_wf M cb cc cn some).
  { apply (source_wf_binary_right M cb cc cn SFAnd right some rhs (or_introl eq_refl) HAnd).
    exact (source_wf_binary_left M cb cc cn SFImpl rhs left reverse
      (or_intror (or_intror eq_refl)) HV (source_full_prv_wellformed M cb cc cn reverse PV)). }
  assert (PWitness:source_full_prv M cb cc cn witness).
  { apply (full_source_CI M cb cc cn pb phixp witness);[|exact PPb|exact PPhi|exact HPair].
    exact (source_wf_binary M cb cc cn SFAnd pb phixp witness (or_introl eq_refl) HPair
      (source_full_prv_wellformed M cb cc cn pb PPb)
      (source_full_prv_wellformed M cb cc cn phixp PPhi)). }
  pose proof (full_source_ExI M cb cc cn inner some p witness WSome PWitness HEx HInst) as PSome.
  assert (PRhs:source_full_prv M cb cc cn rhs).
  { apply (full_source_CI M cb cc cn right some rhs);[|exact PR|exact PSome|exact HAnd].
    exact (source_wf_binary M cb cc cn SFAnd right some rhs (or_introl eq_refl) HAnd
      (source_full_prv_wellformed M cb cc cn right PR) WSome). }
  exact (source_full_modus_ponens M cb cc cn rhs left reverse HV PV PRhs).
Qed.

Print Assumptions source_prop_expression_instantiation.
Print Assumptions source_instantiation_head_member.
Print Assumptions source_full_trace_profile_point.
Print Assumptions source_full_trace_parent.
Print Assumptions source_full_trace_member.
