(** A single changed argument of an actual source-defined binary matrix.
    The unchanged argument uses literal equality, not a deqv premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEnvironments NumericalContexts SourceBounded QuotationHygiene QuotationPayloads
  StableContextSupport SupportedQuotientEnvironments RawQuotientAtomCongruence
  ReplacementMatrixQuotation ReplacementMatrixCongruence ContextualProofs ContextualDeduction.
Unset Implicit Arguments.

Theorem stable_binary_one_argument_implication M (reverse:bool) phi count eb ec en
    x y x' y' u v k l t cb cc cn marker marker_name atom_base eqcode f g implication result :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  ((x=u /\ x'=v /\ y=y') \/ (y=u /\ y'=v /\ x=x')) ->
  quotient_pair_safe M t u v atom_base -> quotation_atom M true u v t atom_base eqcode ->
  quotation_safe M eb ec en k t -> quotation_safe M eb ec en l t ->
  coding_lt M x k -> coding_lt M y k -> coding_lt M x' l -> coding_lt M y' l ->
  binary_matrix_quotation M phi eb ec en x y k t f ->
  binary_matrix_quotation M phi eb ec en x' y' l t g ->
  implication_graph M (if reverse then g else f) (if reverse then f else g) implication ->
  implication_graph M eqcode implication result -> stable_context_support M cb cc cn result.
Proof.
  intros HB HM HMarker HMatch HEqSafe HEq HK HL HX HY HX' HY' HF HG HImp HResult
    db dc dn HIncluded.
  destruct (environment_cons_total M db dc dn eqcode) as [qb [qc [qn HQ]]].
  assert (HMarker' : stable_context_support M qb qc qn marker).
  { apply (stable_context_support_cons M db dc dn eqcode qb qc qn marker HQ).
    exact (stable_context_support_included M cb cc cn db dc dn marker HIncluded HMarker). }
  assert (HEqSupport : stable_context_support M qb qc qn eqcode).
  { apply stable_context_support_member.
    apply (proj2 (context_member_cons M db dc dn eqcode qb qc qn eqcode HQ));now left. }
  assert (HPair : supported_quotient_pair M qb qc qn t u v).
  { exact (supported_quotient_pair_one_base M qb qc qn t u v atom_base eqcode HEqSafe HEq HEqSupport). }
  assert (HPairs : supported_quotient_pair M qb qc qn t x x' /\
      supported_quotient_pair M qb qc qn t y y').
  { destruct HMatch as [[EX [EX' EY]]|[EY [EY' EX]]].
    - split;[now rewrite EX,EX'|left;exact EY].
    - split;[left;exact EX|now rewrite EY,EY']. }
  destruct HPairs as [HPX HPY].
  destruct (binary_matrix_quotation_congruence M phi count eb ec en x x' y y'
    k l t qb qc qn marker marker_name f g HB HM HMarker' HPX HPY HK HL HX HY HX' HY' HF HG)
    as [HForward HBackward].
  assert (HArrow : contextually_provable M qb qc qn implication).
  { destruct reverse;[exact (HBackward implication HImp)|exact (HForward implication HImp)]. }
  destruct (contextual_deduction M db dc dn eqcode qb qc qn implication HQ HArrow)
    as [actual [HActual HProof]].
  assert (result=actual) by exact (code_relation_functional M _ _ result actual HResult HActual).
  now subst result.
Qed.

Print Assumptions stable_binary_one_argument_implication.
