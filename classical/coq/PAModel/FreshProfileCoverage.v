(** Complete pointwise reverse range implication. Fresh witnesses are
    selected after the finite raw membership body is known; the source
    matrix is then quoted above all of them. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeExpressions NumericalProofs
  NumericalQuotation NumericalEquivalence NumericalEnvironments NumericalContexts ContextualProofs
  StableContextSupport SourceBounded SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors
  QuotationPayloads QuotationHygiene QuotationAtomRebase SubstitutionEnvironmentTotal
  RawQuotientAtomCongruence SupportedQuotientEnvironments RawCollectionProfile RawClauseAlpha
  RawDmemWitness ReplacementMatrixQuotation MatrixClauseRenaming HybridImageGraphs ProfileCoverageAtWitnesses
  ContextFreshBounds ReplacementFreshAllocation TemplateNamedSubstitution QuotedSameBaseRules.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem raw_profile_quotient_image_implies_membership M phi count ra rb functionSource functionQ
    eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name cb cc cn
    x0 y ab0 mb0 image qbase q dy :
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  numerical_quotation M functionSource eb ec en functionBase t functionQ ->
  quotation_safe M eb ec en functionBase t -> stable_context_support M cb cc cn functionQ ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  raw_clause_usable_name M eb ec en t a c profileBase u0 ->
  raw_clause_usable_name M eb ec en t a c profileBase v0 -> u0<>v0 ->
  quotation_safe M eb ec en profileBase t ->
  binary_matrix_quotation M phi eb ec en u0 v0 profileBase t theta0 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  stable_context_support M cb cc cn profile ->
  quotation_safe M eb ec en x0 t -> coding_lt M a x0 -> coding_lt M y x0 ->
  quotient_pair_safe M t x0 a ab0 -> quotation_safe M eb ec en mb0 t ->
  coding_lt M x0 mb0 -> coding_lt M y mb0 ->
  hybrid_image_graph M phi eb ec en t a y x0 ab0 mb0 image ->
  membership_graph M t y dy -> stable_context_support M cb cc cn dy ->
  quotient_pair_safe M t y c qbase -> quotation_atom M false y c t qbase q ->
  contextually_provable M cb cc cn image -> contextually_provable M cb cc cn q.
Proof.
  intros HB RA RB GF FQ HF PF HM PM NU0 NV0 HUV HP Q0 GP PP HX0 HAX0 HYX0
    HAB0 HMB0 HX0MB HYMB Image DY PY HQ GQ PImage.
  set (names:=cons cb (cons eb (cons t (cons a (cons c (cons y (cons u0 (cons v0 (cons x0 (cons (zeroM M) nil)))))))))).
  set (x:=replacement_name_bound M names).
  assert (Large:forall value,In value names -> coding_lt M value x).
  { intros value HV;exact (replacement_name_bound_above M names value HV). }
  assert (HCbX:coding_lt M cb x) by (apply Large;unfold names;simpl;tauto).
  assert (HEbX:coding_lt M eb x) by (apply Large;unfold names;simpl;tauto).
  assert (HTX:coding_lt M t x) by (apply Large;unfold names;simpl;tauto).
  assert (HAX:coding_lt M a x) by (apply Large;unfold names;simpl;tauto).
  assert (HCX:coding_lt M c x) by (apply Large;unfold names;simpl;tauto).
  assert (HYX:coding_lt M y x) by (apply Large;unfold names;simpl;tauto).
  assert (HU0X:coding_lt M u0 x) by (apply Large;unfold names;simpl;tauto).
  assert (HV0X:coding_lt M v0 x) by (apply Large;unfold names;simpl;tauto).
  assert (HX0X:coding_lt M x0 x) by (apply Large;unfold names;simpl;tauto).
  assert (H0X:coding_lt M (zeroM M) x) by (apply Large;unfold names;simpl;tauto).
  assert (HSX:quotation_safe M eb ec en x t).
  { split;[exact HTX|exact (environment_below_above_code M eb ec en x HEbX H0X)]. }
  set (lowBase:=succM M x).
  assert (HXLow:coding_lt M x lowBase) by apply coding_lt_succ.
  destruct (quotation_atom_total M false x a t lowBase) as [lowInput GLow].
  set (u:=replacement_name_bound M (cons lowInput (cons x nil))).
  assert (HLU:coding_lt M lowInput u) by (apply replacement_name_bound_above;now left).
  assert (HXU:coding_lt M x u) by (apply replacement_name_bound_above;now right;left).
  destruct (quotation_atom_total M false x a t u) as [qInput GInput].
  destruct (raw_dmem_witness_graph_total M t x a u qInput GInput)
    as (du & inA & eq0 & childInput & bodyInput & RawI).
  set (z:=replacement_name_bound M (cons bodyInput (cons u nil))).
  assert (HBZ:coding_lt M bodyInput z) by (apply replacement_name_bound_above;now left).
  assert (HUZ:coding_lt M u z) by (apply replacement_name_bound_above;now right;left).
  set (k:=succM M z).
  assert (HZK:coding_lt M z k) by apply coding_lt_succ.
  assert (HXZ:coding_lt M x z) by exact (coding_lt_trans M x u z HXU HUZ).
  assert (HXK:coding_lt M x k) by exact (coding_lt_trans M x z k HXZ HZK).
  assert (HX0K:coding_lt M x0 k) by exact (coding_lt_trans M x0 x k HX0X HXK).
  assert (HYK:coding_lt M y k) by exact (coding_lt_trans M y x k HYX HXK).
  assert (HTK:coding_lt M t k) by exact (coding_lt_trans M t x k HTX HXK).
  assert (H0K:coding_lt M (zeroM M) k) by exact (coding_lt_trans M (zeroM M) x k H0X HXK).
  assert (HSK:quotation_safe M eb ec en k t).
  { split;[exact HTK|]. intros i value HV;exact (coding_lt_trans M value x k ((proj2 HSX) i value HV) HXK). }
  destruct (hybrid_image_graph_total M phi eb ec en t a y x0 lowBase k) as [image0 Image0].
  destruct (hybrid_image_graph_total M phi eb ec en t a y x lowBase k) as [imageX ImageX].
  assert (PImage0:contextually_provable M cb cc cn image0).
  { apply (contextual_equivalent_forward M cb cc cn image image0);[|exact PImage].
    apply (hybrid_image_rebase M phi eb ec en t a y x0 ab0 mb0 lowBase k image image0);try assumption.
    repeat split.
    - exact (coding_lt_trans M (zeroM M) x lowBase H0X HXLow).
    - exact (coding_lt_trans M t x lowBase HTX HXLow).
    - exact (coding_lt_trans M x0 x lowBase HX0X HXLow).
    - exact (coding_lt_trans M a x lowBase HAX HXLow). }
  assert (PImageX:contextually_provable M cb cc cn imageX).
  { apply (contextual_equivalent_forward M cb cc cn image0 imageX);[|exact PImage0].
    apply (hybrid_image_alpha M phi eb ec en t a y x0 x lowBase k image0 imageX);try assumption.
    - exact (template_lt_different M (zeroM M) x0 (environment_below_zero M eb ec en x0 (proj2 HX0))).
    - exact (template_lt_different M (zeroM M) x H0X).
    - exact (fun E=>template_lt_different M x0 x HX0X (eq_sym E)).
    - exact (fun E=>template_lt_different M t x0 (proj1 HX0) (eq_sym E)).
    - exact (fun E=>template_lt_different M a x0 HAX0 (eq_sym E)).
    - exact (fun E=>template_lt_different M y x0 HYX0 (eq_sym E)).
    - exact (fun E=>template_lt_different M t x HTX (eq_sym E)).
    - exact (fun E=>template_lt_different M a x HAX (eq_sym E)).
    - exact (fun E=>template_lt_different M y x HYX (eq_sym E)).
    - exact (coding_lt_trans M x0 x lowBase HX0X HXLow).
    - intros i value HV E;subst value;exact (template_lt_different M x0 x0 ((proj2 HX0) i x0 HV) eq_refl).
    - intros i value HV E;subst value;exact (template_lt_different M x x ((proj2 HSX) i x HV) eq_refl). }
  destruct ImageX as (lowInput' & thetaXY & dx & rest & body & GIL & QXY & DX & REST & BODY & EX).
  assert (lowInput'=lowInput) by exact (quotation_atom_functional M false x a t lowBase lowInput' lowInput GIL GLow).
  subst lowInput'.
  destruct (quotation_atom_total M false y c t z) as [qOut GOut].
  assert (POut:contextually_provable M cb cc cn qOut).
  { apply (profile_coverage_at_fresh_witnesses M phi count ra rb functionSource functionQ
      eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name cb cc cn
      x u y z lowBase lowInput qInput du inA eq0 childInput bodyInput thetaXY dx rest body imageX qOut dy);
      try assumption.
    - exact (coding_lt_trans M u0 x u HU0X HXU).
    - exact (coding_lt_trans M v0 x u HV0X HXU).
    - repeat split.
      + exact (coding_lt_trans M (zeroM M) x lowBase H0X HXLow).
      + exact (coding_lt_trans M t x lowBase HTX HXLow).
      + exact HXLow.
      + exact (coding_lt_trans M a x lowBase HAX HXLow). }
  apply (contextual_equivalent_forward M cb cc cn qOut q);[|exact POut].
  destruct HQ as [HQ0 [HTQ [HYQ HCQ]]].
  exact (quotation_atom_rebase M false y c t z qbase qOut q
    (coding_lt_trans M (zeroM M) x z H0X HXZ) HQ0
    (coding_lt_trans M y x z HYX HXZ) (coding_lt_trans M c x z HCX HXZ)
    (coding_lt_trans M t x z HTX HXZ) HYQ HCQ HTQ GOut GQ).
Qed.

Print Assumptions raw_profile_quotient_image_implies_membership.


