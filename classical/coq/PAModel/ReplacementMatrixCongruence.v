(** The actual mixed quotient theorem supplies invariance for exactly the
    source-defined binary matrices used by the Replacement adapter. *)
From PAModel Require Import Model FiniteCoding NumericalEnvironments QuotationHygiene
  SourceBounded SupportedQuotientEnvironments StableContextSupport RawQuotientAtomCongruence
  ContextualEquivalence QuotedBinaryCongruence ReplacementMatrixQuotation.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma replacement_environment_push_below M eb ec en x xb xc xn k :
  environment_below M eb ec en k -> coding_lt M x k ->
  environment_cons M eb ec en x xb xc xn -> environment_below M xb xc xn k.
Proof.
  intros HB HX HC i v HV.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[idx ->]].
  - apply (proj1 (environment_cons_head M eb ec en x xb xc xn v HC)) in HV.
    now subst v.
  - apply (proj1 (environment_cons_tail M eb ec en x xb xc xn idx v HC)) in HV.
    exact (HB idx v HV).
Qed.

Theorem binary_matrix_quotation_congruence M phi count eb ec en x x' y y'
    k l t cb cc cn marker marker_name f g :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  supported_quotient_pair M cb cc cn t x x' -> supported_quotient_pair M cb cc cn t y y' ->
  quotation_safe M eb ec en k t -> quotation_safe M eb ec en l t ->
  coding_lt M x k -> coding_lt M y k -> coding_lt M x' l -> coding_lt M y' l ->
  binary_matrix_quotation M phi eb ec en x y k t f ->
  binary_matrix_quotation M phi eb ec en x' y' l t g ->
  contextual_equivalence M cb cc cn f g.
Proof.
  intros HB HMarker HM HX HY [HTK HEK] [HTL HEL] HXK HYK HXL HYL
    [yb [yc [yn [xb [xc [xn [CY [CX HF]]]]]]]]
    [yb' [yc' [yn' [xb' [xc' [xn' [CY' [CX' HG]]]]]]]].
  apply (quoted_binary_congruence M phi count eb ec en y y' x x'
    yb yc yn yb' yc' yn' xb xc xn xb' xc' xn' k l t cb cc cn marker marker_name f g);
    try assumption.
  - split;[exact HTK|].
    exact (replacement_environment_push_below M yb yc yn x xb xc xn k
      (replacement_environment_push_below M eb ec en y yb yc yn k HEK HYK CY) HXK CX).
  - split;[exact HTL|].
    exact (replacement_environment_push_below M yb' yc' yn' x' xb' xc' xn' l
      (replacement_environment_push_below M eb ec en y' yb' yc' yn' l HEL HYL CY') HXL CX').
Qed.

Print Assumptions replacement_environment_push_below.
Print Assumptions binary_matrix_quotation_congruence.
