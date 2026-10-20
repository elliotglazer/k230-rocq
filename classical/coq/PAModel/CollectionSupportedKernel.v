(** Retain the actual binary requests while replacing the raw support
    clause by the domain-restricted support required by Collection. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions CodeDescent
  NumericalProofs ProofTemplates ProofMacros TemplateCD QuantifierMacros TemplatePropositional ContextualPropositional NamedLeibnizSteps
  NumericalVacuitySteps NumericalKP0 NumericalKP0Eligibility NumericalBootstrap
  NumericalTaggedComprehension TemplateFormulaFresh ExpressionFreshElimination
  FreshNames FreshPropagation NamedBinderFresh NumericalEquality QuotientAtomTemplates RawMarkerExclusions RawMarkerQuantifiers
  RawCollectionProfile CollectionSupportCleanup CollectionMatrixInstance CollectionKernel.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_collection_supported_kernel T A B R C (I:code_expr) P U V Theta Z :=
  E_wex C (E_wa (E_collection_requests T A B R C P U V Theta Z)
    (E_wal V (E_raw_collection_support T A C U V Theta))).

Lemma collection_kernel_cleanup_program T A B R C I P U V Theta Z :
  proof_macro nil
    (E_vac C (E_marker_empty T Z) :: E_vac C (E_wn (E_wel T B)) ::
      E_wim (E_marker_empty T Z) (E_wim (E_wn (E_wel T B))
        (E_wim (E_collection_raw_support T A B R C I U V Theta Z)
          (E_wal V (E_raw_collection_support T A C U V Theta)))) :: nil)
    (E_wim (E_marker_empty T Z) (E_wim (E_wn (E_wel T B))
      (E_wim (E_collection_kernel T A B R C I P U V Theta Z)
        (E_collection_supported_kernel T A B R C I P U V Theta Z)))).
Proof.
  set (H:=E_wa (E_marker_empty T Z) (E_wn (E_wel T B))).
  set (Req:=E_collection_requests T A B R C P U V Theta Z).
  set (Raw:=E_collection_raw_support T A B R C I U V Theta Z).
  set (Clean:=E_wal V (E_raw_collection_support T A C U V Theta)).
  set (inputs:=E_vac C (E_marker_empty T Z) :: E_vac C (E_wn (E_wel T B)) ::
    E_wim (E_marker_empty T Z) (E_wim (E_wn (E_wel T B)) (E_wim Raw Clean)) :: nil).
  assert (HV:proof_macro nil inputs (E_vac C H)).
  { unfold H. apply kp0_vacuous_conjunction;apply PM_input;unfold inputs;cbn;tauto. }
  assert (HB:proof_macro nil inputs (E_wim H (E_wim (E_wa Req Raw) (E_wa Req Clean)))).
  { apply macro_discharge. do 2 apply macro_deduction. apply kp0_md_conjunction.
    - apply tagged_md_left with (b:=Raw),md_hyp;now left.
    - eapply md_mp with (a:=Raw).
      + apply tagged_md_right with (a:=Req),md_hyp;now left.
      + eapply md_mp with (a:=E_wn (E_wel T B)).
        * apply tagged_md_right with (a:=E_marker_empty T Z),md_hyp;now right;left.
        * eapply md_mp with (a:=E_marker_empty T Z).
          -- apply tagged_md_left with (b:=E_wn (E_wel T B)),md_hyp;now right;left.
          -- apply md_global,PM_input;unfold inputs;now right;right;left. }
  pose proof (kp0_parameter_exists inputs C H (E_wa Req Raw) (E_wa Req Clean) HV HB) as HE.
  unfold E_collection_kernel,E_collection_supported_kernel.
  apply macro_discharge. do 3 apply macro_deduction.
  eapply md_mp with (a:=E_wex C (E_wa Req Raw));[apply md_hyp;now left|].
  eapply md_mp with (a:=H).
  - unfold H. apply kp0_md_conjunction;apply md_hyp;[now right;right;left|now right;left].
  - apply md_global;exact HE.
Qed.

Lemma collection_fresh_one_nonzero M rho name :
  expression_fresh M rho name (CEconst 1) -> name<>zeroM M.
Proof.
  intro HF.
  assert (HG:membership_graph M (zeroM M) (zeroM M) (code_numeral M 1)).
  { exists (zeroM M). split;[apply pair_zero|].
    rewrite (Arithmetic.mul_comm M),Arithmetic.mul_zero,Arithmetic.add_zero. reflexivity. }
  pose proof (proj1 (formula_fresh_membership M (zeroM M) (zeroM M)
    (code_numeral M 1) name HG (HF _ eq_refl))) as HN.
  congruence.
Qed.

Lemma collection_matrix_fresh_nonzero M rho name T A B R I U V Theta Z :
  expression_fresh M rho name (E_collection_choices T A B R I U V Theta Z) ->
  name<>zeroM M.
Proof.
  intro HF. unfold E_collection_choices,E_or in HF.
  apply expression_fresh_implication_parts in HF. destruct HF as [HF _].
  apply expression_fresh_implication_parts in HF. destruct HF as [_ HF].
  exact (collection_fresh_one_nonzero M rho name HF).
Qed.

Theorem numerical_collection_supported_kernel M i v t a b r u theta z m :
  i<>zeroM M -> v<>i -> t<>i -> a<>i -> b<>i -> r<>i -> u<>i -> z<>i ->
  i<>r -> v<>r -> u<>r -> z<>r ->
  v<>zeroM M -> t<>v -> b<>v -> z<>zeroM M -> t<>z ->
  formula_fresh M theta i -> named_binder_absent M theta r ->
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  exists k p f,
    k<>i /\ k<>v /\ k<>r /\ i<>p /\ v<>p /\ k<>p /\ p<>r /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    code_relation M (collection_kernel_parameters M i v t a b r u theta z p k)
      (E_wim (E_marker_empty (CEvar 2) (CEvar 8))
        (E_wim (E_wn (E_wel (CEvar 2) (CEvar 4)))
          (E_collection_supported_kernel (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
            (CEvar 10) (CEvar 0) (CEvar 9) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8)))) f /\
    numerically_provable M f.
Proof.
  intros H0 HVI HTI HAI HBI HRI HUI HZI HIR HVR HUR HZR HV0 HTV HBV HZ0 HTZ HTheta HTR HM.
  destruct (numerical_collection_kernel M i v t a b r u theta z m
    H0 HVI HTI HAI HBI HRI HUI HZI HIR HVR HUR HZR HTheta HTR HM)
    as (k & p & old & HKI & HKV & HKR & HIP & HVP & HKP & HPR & HP0 & HMK & HMP & HO & PO).
  set (rho:=collection_kernel_parameters M i v t a b r u theta z p k).
  assert (HM':code_relation M rho E_collection_parameter_matrix m) by exact HM.
  assert (HFK:expression_fresh M rho k E_collection_parameter_matrix).
  { intros f HF. assert (E:f=m) by exact (code_relation_functional M _ rho f m HF HM').
    now subst f. }
  pose proof (collection_matrix_fresh_nonzero M rho k (CEvar 2) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) HFK) as HK0.
  destruct (collection_matrix_fresh_parts M rho k (CEvar 2) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) HFK)
    as (_ & _ & _ & HBK & HTK & _ & HZK & _).
  set (Empty:=E_marker_empty (CEvar 2) (CEvar 8)).
  set (NotB:=E_wn (E_wel (CEvar 2) (CEvar 4))).
  set (Target:=E_collection_supported_kernel (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
    (CEvar 10) (CEvar 0) (CEvar 9) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8)).
  assert (HC:ns_proof M rho (E_wim Empty (E_wim NotB (E_wim E_collection_parameter_kernel Target)))).
  { apply (ns_proof_macro M rho
      (E_vac (CEvar 10) Empty :: E_vac (CEvar 10) NotB ::
       E_wim Empty (E_wim NotB (E_wim
        (E_collection_raw_support (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 10)
          (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8))
        (E_wal (CEvar 1) (E_raw_collection_support (CEvar 2) (CEvar 3) (CEvar 10)
          (CEvar 6) (CEvar 1) (CEvar 7))))) :: nil)).
    - intros e [<-|[<-|[<-|[]]]].
      + apply (kp0_expression_fresh_vacuity M rho (CEvar 10) Empty k eq_refl).
        unfold Empty. apply expression_fresh_universal;[exact HZK|].
        apply expression_fresh_negation;[exact HK0|].
        apply expression_fresh_atom;[now left|exact HZK|exact HTK].
      + apply (kp0_expression_fresh_vacuity M rho (CEvar 10) NotB k eq_refl).
        unfold NotB. apply expression_fresh_negation;[exact HK0|].
        apply expression_fresh_atom;[now left|exact HTK|exact HBK].
      + apply (numerical_collection_support_cleanup M rho (CEvar 2) (CEvar 3) (CEvar 4)
          (CEvar 5) (CEvar 10) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8)
          (CEvar 8) t i v z eq_refl eq_refl eq_refl eq_refl H0 HV0 HZ0 HTZ).
        * intros x HX. change (x=t) in HX. now subst x.
        * intros x HX. change (x=a) in HX. now subst x.
        * intros x HX. change (x=b) in HX. now subst x.
        * intros x HX. change (x=u) in HX. now subst x.
        * intros x HX. change (x=v) in HX. now subst x.
        * intros x HX. change (x=theta) in HX. now subst x.
        * intros x HX. change (x=t) in HX. now subst x.
        * intros x HX. change (x=b) in HX. now subst x.
    - apply collection_kernel_cleanup_program. }
  assert (PBefore:ns_proof M rho E_collection_parameter_kernel).
  { intros f HF. assert (E:f=old) by exact (code_relation_functional M _ rho f old HF HO).
    now subst f. }
  assert (PAfter:ns_proof M rho (E_wim Empty (E_wim NotB Target))).
  { apply (ns_proof_macro M rho (E_collection_parameter_kernel ::
      E_wim Empty (E_wim NotB (E_wim E_collection_parameter_kernel Target)) :: nil)).
    - intros e [<-|[<-|[]]];assumption.
    - apply macro_discharge. do 2 apply macro_deduction.
      eapply md_mp with (a:=E_collection_parameter_kernel);[apply md_global,PM_input;now left|].
      eapply md_mp with (a:=NotB);[apply md_hyp;now left|].
      eapply md_mp with (a:=Empty);[apply md_hyp;now right;left|].
      apply md_global,PM_input;now right;left. }
  destruct (code_relation_total M (E_wim Empty (E_wim NotB Target)) rho) as [f HF].
  exists k,p,f. repeat split;try assumption. exact (PAfter f HF).
Qed.

Print Assumptions collection_kernel_cleanup_program.
Print Assumptions numerical_collection_supported_kernel.
