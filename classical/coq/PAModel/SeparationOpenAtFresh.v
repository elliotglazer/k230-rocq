(** Assemble the open Separation image at an outer name fresh in the
    marker. The only remaining mathematical input is the explicit raw
    domain-Separation certificate. All representative allocation is fixed
    PA arithmetic and every quotation is an internal numerical graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions ProofTemplates
  NumericalProofs NumericalEnvironments NumericalQuotation QuotationHygiene QuotationBinderFresh
  SourceBounded SourceBoundMonotone SetFormulaCodes QuotationPayloads QuotationFixedSource
  RawQuotientAtomCongruence SupportedQuotientEnvironments FreshNames TemplateFormulaFresh
  NumericalEquivalence NumericalVacuitySteps NamedBinderFresh
  SeparationAllocation RawSeparationContract SelectionFreshness QuotedCanonicalContainer
  CanonicalSeparationGraph ConditionalAllComposition QuotedSameContainer DomainSeparationImage SelectionMemberRebase.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem quoted_separation_at_fresh M marker :
  raw_empty_marker_graph M (code_numeral M 1) (code_numeral M 2) marker ->
  raw_domain_separation_certificates M marker ->
  forall phi bound eb ec en a mb mc mn theta left right q,
  source_bounded M phi bound -> quotation_safe M eb ec en a (code_numeral M 1) ->
  environment_cons M eb ec en (succM M (succM M a)) mb mc mn ->
  numerical_quotation M phi mb mc mn (separation_base M a) (code_numeral M 1) theta ->
  formula_fresh M marker a ->
  quotation_atom M false (succM M (succM M a)) (succM M a)
    (code_numeral M 1) (separation_base M a) left ->
  quotation_atom M false (succM M (succM M a)) a
    (code_numeral M 1) (separation_base M a) right ->
  domain_separation_graph M a theta left right q -> numerical_implies M marker q.
Proof.
  intros HMarker HRaw phi bound eb ec en a mb mc mn theta left right q HB HS HM HTheta HMa HL HR HQ.
  set (c:=succM M a). set (z:=succM M c). set (base:=succM M z).
  set (w:=separation_witness_name M a marker theta).
  destruct (separation_named_bounds M a (proj1 HS)) as [H0a [Hac [Hcz [Hzbase H2c]]]].
  change (coding_lt M a c) in Hac. change (coding_lt M c z) in Hcz.
  change (coding_lt M z base) in Hzbase. change (coding_lt M (code_numeral M 2) c) in H2c.
  destruct (separation_witness_bounds M a marker theta) as [Hbasew [Hmarkerw Hthetaw]].
  change (coding_lt M base w) in Hbasew.
  assert (Haz : coding_lt M a z) by exact (coding_lt_trans M a c z Hac Hcz).
  assert (Habase : coding_lt M a base) by exact (coding_lt_trans M a z base Haz Hzbase).
  assert (Hcbase : coding_lt M c base) by exact (coding_lt_trans M c z base Hcz Hzbase).
  assert (Haw : coding_lt M a w) by exact (coding_lt_trans M a base w Habase Hbasew).
  assert (Hcw : coding_lt M c w) by exact (coding_lt_trans M c base w Hcbase Hbasew).
  assert (Hzw : coding_lt M z w) by exact (coding_lt_trans M z base w Hzbase Hbasew).
  assert (H0c : coding_lt M (zeroM M) c) by exact (coding_lt_trans M _ a c H0a Hac).
  assert (H0z : coding_lt M (zeroM M) z) by exact (coding_lt_trans M _ a z H0a Haz).
  assert (H0base : coding_lt M (zeroM M) base) by exact (coding_lt_trans M _ a base H0a Habase).
  assert (H0w : coding_lt M (zeroM M) w) by exact (coding_lt_trans M _ a w H0a Haw).
  assert (H1c : coding_lt M (code_numeral M 1) c) by exact (coding_lt_trans M _ a c (proj1 HS) Hac).
  assert (H1z : coding_lt M (code_numeral M 1) z) by exact (coding_lt_trans M _ a z (proj1 HS) Haz).
  assert (H1base : coding_lt M (code_numeral M 1) base) by exact (coding_lt_trans M _ a base (proj1 HS) Habase).
  assert (H1w : coding_lt M (code_numeral M 1) w) by exact (coding_lt_trans M _ a w (proj1 HS) Haw).
  assert (H2z : coding_lt M (code_numeral M 2) z) by exact (coding_lt_trans M _ c z H2c Hcz).
  destruct (separation_witness_quotes M phi eb ec en a marker theta HS)
    as [wb [wc [wn [f [HW [HSW [HF [HMw [HThetaW HNoW]]]]]]]]].
  change (environment_cons M eb ec en w wb wc wn) in HW.
  change (quotation_safe M wb wc wn (succM M w) (code_numeral M 1)) in HSW.
  change (numerical_quotation M phi wb wc wn (succM M w) (code_numeral M 1) f) in HF.
  change (formula_fresh M marker w) in HMw. change (formula_fresh M theta w) in HThetaW.
  assert (HSZ : quotation_safe M mb mc mn base (code_numeral M 1)).
  { exact (quotation_safe_cons M eb ec en z _ mb mc mn (separation_safe_above M eb ec en a z _ HS Haz) HM). }
  assert (HFreshA : formula_fresh M f a).
  { exact (separation_quote_fresh_at M phi eb ec en w wb wc wn _ (succM M w) f a HW HF
      (proj2 HS) Haw (coding_lt_trans M a w _ Haw (coding_lt_succ M w)) H0a (proj1 HS)). }
  assert (HFreshC : formula_fresh M f c).
  { exact (separation_quote_fresh_at M phi eb ec en w wb wc wn _ (succM M w) f c HW HF
      (proj2 (separation_safe_above M eb ec en a c _ HS Hac)) Hcw
      (coding_lt_trans M c w _ Hcw (coding_lt_succ M w)) H0c H1c). }
  assert (HFreshZ : formula_fresh M f z).
  { exact (separation_quote_fresh_at M phi eb ec en w wb wc wn _ (succM M w) f z HW HF
      (proj2 (separation_safe_above M eb ec en a z _ HS Haz)) Hzw
      (coding_lt_trans M z w _ Hzw (coding_lt_succ M w)) H0z H1z). }
  assert (HMc : formula_fresh M marker c) by exact (raw_marker_above_fresh M _ _ marker c HMarker H2c).
  assert (HMz : formula_fresh M marker z) by exact (raw_marker_above_fresh M _ _ marker z HMarker H2z).
  set (rho:=a .: w .: f .: theta .: fun _=>zeroM M).
  set (A:=CEvar 0). set (C:=CEadd A (CEconst 1)). set (X:=CEadd C (CEconst 1)).
  set (K:=CEadd X (CEconst 1)). set (W:=CEvar 1). set (P:=CEvar 2). set (Q:=CEvar 3).
  assert (EA : code_relation M rho A a) by reflexivity.
  assert (EC : code_relation M rho C c) by exact (code_graph_fresh_successor M rho A a EA).
  assert (EX : code_relation M rho X z) by exact (code_graph_fresh_successor M rho C c EC).
  assert (EK : code_relation M rho K base) by exact (code_graph_fresh_successor M rho X z EX).
  assert (EP : code_relation M rho P f) by reflexivity.
  assert (EQ : code_relation M rho Q theta) by reflexivity.
  assert (EW : code_relation M rho W w) by reflexivity.
  assert (ET : code_relation M rho (CEconst 1) (code_numeral M 1)) by reflexivity.
  assert (HRFresh : expression_fresh M rho z (E_raw_selection_container (CEconst 1) A C W P)).
  { apply raw_member_selection_body_fresh.
    - intro E. rewrite E in H0z. exact (coding_not_lt_zero M _ H0z).
    - intros v HV. change (v=code_numeral M 1) in HV. subst v. exact (separation_lt_neq M _ _ H1z).
    - intros v HV. assert (v=a) by exact (code_relation_functional M A rho v a HV EA). subst v.
      exact (separation_lt_neq M _ _ Haz).
    - intros v HV. assert (v=c) by exact (code_relation_functional M C rho v c HV EC). subst v.
      exact (separation_lt_neq M _ _ Hcz).
    - intros v HV. change (v=w) in HV. subst v. intro E. exact (separation_lt_neq M z w Hzw (Logic.eq_sym E)).
    - intros v HV. change (v=f) in HV. now subst v. }
  set (Raw:=E_wex C (E_raw_selection_container (CEconst 1) A C W P)).
  set (Target:=E_wex C (E_selection_container_at (CEconst 1) X A C K Q)).
  destruct (code_relation_total M (E_wim (E_wel (CEconst 1) A) Raw) rho) as [rawstep ERawStep].
  assert (PRaw : numerical_implies M marker rawstep).
  { apply (HRaw a w f (proj1 HS) Hbasew HFreshA HFreshC).
    - intros y HY. exact (numerical_quotation_binder_fresh M phi wb wc wn (succM M w) _ f y HF HY).
    - change (code_relation M rho (code_subst
        (CEvar 0 .: CEvar 1 .: CEvar 2 .: fun _=>CEconst 0)
        (E_raw_domain_separation (CEvar 0) (CEvar 1) (CEvar 2))) rawstep) in ERawStep.
      apply (proj1 (code_subst_graph M rho (CEvar 0 .: CEvar 1 .: CEvar 2 .: fun _=>CEconst 0)
        (raw_separation_parameters M a w f) ltac:(intros [|[|[|i]]];reflexivity) _ rawstep)).
      exact ERawStep. }
  destruct (code_relation_total M (E_wim Raw Target) rho) as [transfer ETransfer].
  assert (PTransfer : numerical_implies M marker transfer).
  { apply (numerical_quoted_canonical_container M rho (CEconst 1) X A C W K P Q phi bound
      eb ec en w z a c base wb wc wn mb mc mn (succM M w) base (code_numeral M 1)
      marker (code_numeral M 2) f theta transfer).
    - exact (source_bounded_monotone M phi bound (succM M bound) HB
        (coding_lt_trans M bound (succM M bound) _ (coding_lt_succ M _) (coding_lt_succ M _))).
    - exact HMarker.
    - split;[apply coding_zero_lt_succ|].
      split;[exact (coding_lt_trans M _ w _ H1w (coding_lt_succ M _))|].
      split;[exact (coding_lt_trans M _ w _ Hzw (coding_lt_succ M _))|apply coding_lt_succ].
    - exact HW.
    - exact HM.
    - exact HSW.
    - exact HSZ.
    - exact HF.
    - exact HTheta.
    - exact ET.
    - exact EX.
    - exact EA.
    - exact EC.
    - exact EW.
    - exact EK.
    - exact EP.
    - exact EQ.
    - repeat split;assumption.
    - repeat split;assumption.
    - repeat split;assumption.
    - repeat split;assumption.
    - exact HMw.
    - exact HThetaW.
    - exact HMz.
    - exact HMc.
    - exact HRFresh.
    - exact ETransfer. }
  assert (EWhole : code_relation M rho
    (E_wal A (E_wim (E_wel (CEconst 1) A) Target)) q).
  { exact (canonical_separation_graph M rho (CEconst 1) A C X K Q a theta left right q
      ET EA EC EX EK EQ HL HR HQ). }
  destruct (code_relation_total M (E_wel (CEconst 1) A) rho) as [domain EDomain].
  destruct (code_relation_total M Raw rho) as [raw ERaw].
  destruct (code_relation_total M Target rho) as [target ETarget].
  destruct (code_relation_total M (E_wim (E_wel (CEconst 1) A) Target) rho) as [step EStep].
  apply (numerical_conditional_all_composition M marker domain raw target rawstep transfer step a q).
  - exact (proj1 (expression_implication_iff M rho _ _ domain raw rawstep EDomain ERaw) ERawStep).
  - exact PRaw.
  - exact (proj1 (expression_implication_iff M rho _ _ raw target transfer ERaw ETarget) ETransfer).
  - exact PTransfer.
  - exact (proj1 (expression_implication_iff M rho _ _ domain target step EDomain ETarget) EStep).
  - exact (proj1 (expression_universal_iff M rho _ _ a step q EA EStep) EWhole).
  - exact HMa.
Qed.

Print Assumptions quoted_separation_at_fresh.
