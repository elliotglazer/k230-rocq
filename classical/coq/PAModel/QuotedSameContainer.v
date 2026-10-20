(** Raw-domain Separation transfers to literal quotient membership on the
    same container. The raw existence statement remains an explicit input;
    bounded source quotation supplies the required representative invariance. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates NumericalProofs
  NumericalEnvironments NumericalQuotation QuotationHygiene SourceBounded FreshNames
  RawQuotientAtomCongruence SupportedQuotientEnvironments QuotationPayloads SetFormulaCodes
  NumericalEquivalence NumericalVacuitySteps NamedExistential TemplateFormulaFresh
  QuotientSeparationWitness QuotedSeparationPoint LiteralMemberSeparationPoint SameContainerTransfer.
Unset Implicit Arguments.

Definition E_raw_selection_container T A C W P :=
  E_wa (E_wel T C) (E_raw_member_selection T A C W P).
Definition E_quotient_selection_container T X A C W Q :=
  E_wa (E_wel T C)
    (E_wal X (E_wim (E_wel T X) (E_literal_member_selection T X A C W Q))).

Theorem numerical_quoted_same_container M env T X A C W P Q
    phi count eb ec en w z c wb wc wn zb zc zn k l t marker marker_name f g result :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker ->
  quotient_pair_safe M t z w (succM M w) ->
  environment_cons M eb ec en w wb wc wn -> environment_cons M eb ec en z zb zc zn ->
  quotation_safe M wb wc wn k t -> quotation_safe M zb zc zn l t ->
  numerical_quotation M phi wb wc wn k t f -> numerical_quotation M phi zb zc zn l t g ->
  code_relation M env T t -> code_relation M env X z -> code_relation M env W w ->
  code_relation M env C c -> code_relation M env P f -> code_relation M env Q g ->
  formula_fresh M marker w -> formula_fresh M g w ->
  formula_fresh M marker z -> formula_fresh M marker c ->
  expression_fresh M env z (E_raw_selection_container T A C W P) ->
  code_relation M env
    (E_wim (E_wex C (E_raw_selection_container T A C W P))
      (E_wex C (E_quotient_selection_container T X A C W Q))) result ->
  numerical_implies M marker result.
Proof.
  intros HB HM HS HW HZ HK HL HF HG ET EX EW EC EP EQ HMw HQw HMz HMc HRFresh HResult.
  set (R:=E_raw_member_selection T A C W P).
  set (S:=E_literal_member_selection T X A C W Q).
  set (B:=E_raw_selection_container T A C W P).
  set (N:=E_quotient_selection_container T X A C W Q).
  destruct (code_relation_total M R env) as [rawall ER].
  destruct (code_relation_total M S env) as [point ES].
  destruct (code_relation_total M B env) as [rawbody EB].
  destruct (code_relation_total M N env) as [targetbody EN].
  destruct (code_relation_total M (E_wel T C) env) as [domain ED].
  destruct (code_relation_total M (E_wel T X) env) as [tested_domain EZD].
  destruct (code_relation_total M (E_wim (E_wel T X) S) env) as [guarded EG].
  destruct (code_relation_total M (E_wal X (E_wim (E_wel T X) S)) env) as [allpoint EA].
  destruct (code_relation_total M (E_wim R S) env) as [pointstep EPS].
  destruct (code_relation_total M (E_wim B N) env) as [bodystep EBS].
  destruct (code_relation_total M (E_wex C B) env) as [rawexists ERE].
  destruct (code_relation_total M (E_wex C N) env) as [targetexists ETE].
  assert (HRaw : quotation_binary M SFAnd domain rawall rawbody).
  { exact (proj1 (selection_expression_conjunction M env (E_wel T C) R domain rawall rawbody ED ER) EB). }
  assert (HStep : implication_graph M rawall point pointstep).
  { exact (proj1 (expression_implication_iff M env R S rawall point pointstep ER ES) EPS). }
  assert (PStep : numerical_implies M marker pointstep).
  { exact (numerical_literal_member_selection M env T X A C W P Q phi count eb ec en w z
      wb wc wn zb zc zn k l t marker marker_name f g pointstep HB HM HS HW HZ HK HL
      HF HG ET EX EW EP EQ HMw HQw EPS). }
  assert (HGuard : implication_graph M tested_domain point guarded).
  { exact (proj1 (expression_implication_iff M env (E_wel T X) S tested_domain point guarded EZD ES) EG). }
  assert (HAll : universal_graph M z guarded allpoint).
  { exact (proj1 (expression_universal_iff M env X (E_wim (E_wel T X) S) z guarded allpoint EX EG) EA). }
  assert (HTarget : quotation_binary M SFAnd domain allpoint targetbody).
  { exact (proj1 (selection_expression_conjunction M env (E_wel T C)
      (E_wal X (E_wim (E_wel T X) S)) domain allpoint targetbody ED EA) EN). }
  assert (HBody : implication_graph M rawbody targetbody bodystep).
  { exact (proj1 (expression_implication_iff M env B N rawbody targetbody bodystep EB EN) EBS). }
  assert (PBody : numerical_implies M marker bodystep).
  { exact (numerical_same_container_body M marker rawall domain rawbody point pointstep z tested_domain
      guarded allpoint targetbody bodystep HRaw HStep PStep HMz (HRFresh rawbody EB)
      HGuard HAll HTarget HBody). }
  assert (HRawExists : named_exists_graph M c rawbody rawexists).
  { exact (proj1 (named_exists_expression M env C B c rawbody rawexists EC EB) ERE). }
  assert (HTargetExists : named_exists_graph M c targetbody targetexists).
  { exact (proj1 (named_exists_expression M env C N c targetbody targetexists EC EN) ETE). }
  assert (HFinal : implication_graph M rawexists targetexists result).
  { exact (proj1 (expression_implication_iff M env (E_wex C B) (E_wex C N)
      rawexists targetexists result ERE ETE) HResult). }
  exact (numerical_same_container_exists M marker c rawbody targetbody rawexists targetexists result
    bodystep HMc HBody PBody HRawExists HTargetExists HFinal).
Qed.

Print Assumptions numerical_quoted_same_container.
