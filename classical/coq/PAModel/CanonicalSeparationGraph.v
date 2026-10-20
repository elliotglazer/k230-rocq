(** The named expression assembled by the raw-to-quotient transfer is
    literally the open Separation image, including both domain guards. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  QuotationPayloads QuotationFixedSource SetFormulaCodes DomainSeparationImage
  SelectionMemberRebase.
Unset Implicit Arguments.

Definition E_open_selection T A C X K Q :=
  E_wal A (E_wim (E_wel T A) (E_wex C (E_selection_container_at T X A C K Q))).

Theorem canonical_separation_graph M env T A C X K Q a theta left right q :
  code_relation M env T (code_numeral M 1) -> code_relation M env A a ->
  code_relation M env C (succM M a) -> code_relation M env X (succM M (succM M a)) ->
  code_relation M env K (succM M (succM M (succM M a))) -> code_relation M env Q theta ->
  quotation_atom M false (succM M (succM M a)) (succM M a)
    (code_numeral M 1) (succM M (succM M (succM M a))) left ->
  quotation_atom M false (succM M (succM M a)) a
    (code_numeral M 1) (succM M (succM M (succM M a))) right ->
  domain_separation_graph M a theta left right q ->
  code_relation M env (E_open_selection T A C X K Q) q.
Proof.
  intros ET EA EC EX EK EQ HL HR
    [rhs [forward [backward [iffcode [allx [exb [HRhs [HF [HB [HI [HX [HE HA]]]]]]]]]]]].
  assert (EL : code_relation M env (E_member_at T X C K) left).
  { exact (proj2 (member_at_graph M env T X C K _ _ _ _ left ET EX EC EK) HL). }
  assert (ER : code_relation M env (E_member_at T X A K) right).
  { exact (proj2 (member_at_graph M env T X A K _ _ _ _ right ET EX EA EK) HR). }
  assert (ERhs : code_relation M env (E_wa (E_member_at T X A K) Q) rhs).
  { exact (proj2 (quotation_binary_substitution_graph M env SFAnd _ _ _ _ _ ER EQ) HRhs). }
  assert (EF : code_relation M env (E_wim (E_member_at T X C K) (E_wa (E_member_at T X A K) Q)) forward).
  { exact (proj2 (quotation_binary_substitution_graph M env SFImpl _ _ _ _ _ EL ERhs) HF). }
  assert (EB : code_relation M env (E_wim (E_wa (E_member_at T X A K) Q) (E_member_at T X C K)) backward).
  { exact (proj2 (quotation_binary_substitution_graph M env SFImpl _ _ _ _ _ ERhs EL) HB). }
  assert (EI : code_relation M env (E_selection_at T X A C K Q) iffcode).
  { exact (proj2 (quotation_binary_substitution_graph M env SFAnd _ _ _ _ _ EF EB) HI). }
  assert (EAll : code_relation M env
    (E_wal X (E_wim (E_wel T X) (E_selection_at T X A C K Q))) allx).
  { exact (proj2 (quotation_quantifier_substitution_graph M env true X T (E_selection_at T X A C K Q)
      _ _ _ _ EX ET EI) HX). }
  assert (EEx : code_relation M env (E_wex C (E_selection_container_at T X A C K Q)) exb).
  { exact (proj2 (quotation_quantifier_substitution_graph M env false C T
      (E_wal X (E_wim (E_wel T X) (E_selection_at T X A C K Q))) _ _ _ _ EC ET EAll) HE). }
  exact (proj2 (quotation_quantifier_substitution_graph M env true A T
    (E_wex C (E_selection_container_at T X A C K Q)) _ _ _ _ EA ET EEx) HA).
Qed.

Print Assumptions canonical_separation_graph.
