(** Base-independence of the actual fixed quotient atom templates, proved
    with internal K derivations. This is the atomic case needed for a later
    induction over arbitrary internally coded source formulas. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEquivalence FiniteTemplateEvaluation FiniteTemplateRebase
  QuotientAtomTemplates QuotationPayloads QuotationRules NumericalQuotation
  QuotationFunctionality QuotationHygiene NumericalEnvironments
  SubstitutionEnvironmentTotal SetFormulaCodes.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition quotation_atom_values {A : Type} (x y domain : A) := domain .: x .: fun _ : nat=>y.

Lemma quotation_atom_evaluation M equality x y domain k f :
  quotation_atom M equality x y domain k f <->
  template_evaluation M
    (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2)
    (quotation_atom_values x y domain) k f.
Proof.
  unfold quotation_atom,quotation_atom_expression,quotient_equal_template,quotient_member_template.
  destruct equality;apply template_evaluation_graph.
  - intros [|[|i]];reflexivity.
  - reflexivity.
  - intros [|[|i]];reflexivity.
  - reflexivity.
Qed.

Theorem quotation_atom_rebase M equality x y domain k l f g :
  coding_lt M (zeroM M) k -> coding_lt M (zeroM M) l ->
  coding_lt M x k -> coding_lt M y k -> coding_lt M domain k ->
  coding_lt M x l -> coding_lt M y l -> coding_lt M domain l ->
  quotation_atom M equality x y domain k f -> quotation_atom M equality x y domain l g ->
  numerical_equivalent M f g.
Proof.
  intros Hk0 Hl0 Hxk Hyk Hdk Hxl Hyl Hdl HF HG.
  apply (finite_template_rebase M
    (if equality then source_deqv $0 $1 $2 else source_dmem $0 $1 $2)
    (quotation_atom_values x y domain) k l f g).
  - apply template_hygienic_below;[exact Hk0|]. intros [|[|i]];assumption.
  - apply template_hygienic_below;[exact Hl0|]. intros [|[|i]];assumption.
  - exact (proj1 (quotation_atom_evaluation M equality x y domain k f) HF).
  - exact (proj1 (quotation_atom_evaluation M equality x y domain l g) HG).
Qed.

Theorem numerical_quotation_atom_rebase M equality a b source eb ec en k l domain f g :
  sf_relation M (quotation_source_atom equality) a b source ->
  quotation_safe M eb ec en k domain -> quotation_safe M eb ec en l domain ->
  numerical_quotation M source eb ec en k domain f ->
  numerical_quotation M source eb ec en l domain g -> numerical_equivalent M f g.
Proof.
  intros HS [HDk HEk] [HDl HEl] HF HG.
  destruct (numerical_quotation_atom_inv M equality a b source eb ec en k domain f HS HF)
    as [x [y [HX [HY Hf]]]].
  destruct (numerical_quotation_atom_inv M equality a b source eb ec en l domain g HS HG)
    as [x' [y' [HX' [HY' Hg]]]].
  assert (x'=x) by exact (environment_lookup_functional M eb ec en a x' x HX' HX).
  assert (y'=y) by exact (environment_lookup_functional M eb ec en b y' y HY' HY).
  subst x' y'. apply (quotation_atom_rebase M equality x y domain k l f g);try assumption.
  - exact (environment_below_zero M eb ec en k HEk).
  - exact (environment_below_zero M eb ec en l HEl).
  - exact (HEk a x HX).
  - exact (HEk b y HY).
  - exact (HEl a x HX).
  - exact (HEl b y HY).
Qed.

Print Assumptions quotation_atom_rebase.
Print Assumptions numerical_quotation_atom_rebase.
