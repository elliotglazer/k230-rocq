(** Exact source-skeleton interface for the pointwise Replacement range. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalQuotation NumericalEnvironments QuotationFunctionality QuotationPayloads QuotationSchemaSkeleton
  SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors SourceBounded
  DomainReplacementImage ReplacementMatrixQuotation HybridImageGraphs NamedExistential
  QuotationFixedSource ContextualGuardedQuantifiers.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition replacement_image_skeleton := SkeletonQuantifier false
  (skeleton_and (SkeletonAtom false 0 3) (SkeletonHole 2)).
Definition replacement_pointwise_skeleton := skeleton_iff (SkeletonAtom false 0 1) replacement_image_skeleton.
Definition replacement_output_skeleton := SkeletonQuantifier true replacement_pointwise_skeleton.
Definition replacement_collector_skeleton := SkeletonQuantifier false replacement_output_skeleton.
Definition replacement_range_skeleton := SkeletonQuantifier true replacement_collector_skeleton.

Lemma skeleton_quotation_functional M s sources b c n k t f g :
  skeleton_quotation M s sources b c n k t f -> skeleton_quotation M s sources b c n k t g -> f=g.
Proof.
  intros HF HG. destruct (code_relation_total M (skeleton_code s) sources) as [source HS].
  exact (numerical_quotation_functional M source b c n k t f g
    (proj1 (skeleton_quotation_correct M s sources source HS b c n k t f) HF)
    (proj1 (skeleton_quotation_correct M s sources source HS b c n k t g) HG)).
Qed.

Lemma skeleton_quotation_total M s sources b c n k t :
  exists f,skeleton_quotation M s sources b c n k t f.
Proof.
  destruct (code_relation_total M (skeleton_code s) sources) as [source HS].
  destruct (numerical_quotation_total M source b c n k t) as [f HF].
  exists f;exact (proj2 (skeleton_quotation_correct M s sources source HS b c n k t f) HF).
Qed.

Theorem replacement_pointwise_skeleton_data M phi bound ra rb rc eb ec en a c y
    ab ac an cb cc cn yb yc yn base t result :
  source_bounded M phi bound -> schema_renaming M RepC phi rc ->
  environment_cons M eb ec en a ab ac an -> environment_cons M ab ac an c cb cc cn ->
  environment_cons M cb cc cn y yb yc yn ->
  skeleton_quotation M replacement_pointwise_skeleton (schema_env3 ra rb rc) yb yc yn base t result ->
  exists left image forward backward,
    quotation_atom M false y c t base left /\
    hybrid_image_graph M phi eb ec en t a y base (succM M base) (succM M base) image /\
    implication_graph M left image forward /\ implication_graph M image left backward /\
    quotation_binary M SFAnd forward backward result.
Proof.
  intros HB HC HA HCol HY HResult.
  change (exists forward backward,
    skeleton_quotation M (skeleton_impl (SkeletonAtom false 0 1) replacement_image_skeleton)
      (schema_env3 ra rb rc) yb yc yn base t forward /\
    skeleton_quotation M (skeleton_impl replacement_image_skeleton (SkeletonAtom false 0 1))
      (schema_env3 ra rb rc) yb yc yn base t backward /\ quotation_binary M SFAnd forward backward result) in HResult.
  destruct HResult as (forward & backward & HF & HBw & HAnd).
  destruct HF as (left & image & HL & HI & HFor).
  destruct HBw as (image' & left' & HI' & HL' & HBack).
  assert (EI:image'=image) by exact (skeleton_quotation_functional M replacement_image_skeleton
    (schema_env3 ra rb rc) yb yc yn base t image' image HI' HI).
  assert (EL:left'=left) by exact (skeleton_quotation_functional M (SkeletonAtom false 0 1)
    (schema_env3 ra rb rc) yb yc yn base t left' left HL' HL).
  subst image' left'.
  assert (GLeft:quotation_atom M false y c t base left).
  { apply (replacement_skeleton_atom_values M (schema_env3 ra rb rc) yb yc yn base t false 0 1 y c left).
    - exact (proj2 (environment_cons_head M cb cc cn y yb yc yn y HY) eq_refl).
    - change (environment_lookup M yb yc yn (succM M (zeroM M)) c).
      apply (proj2 (environment_cons_tail M cb cc cn y yb yc yn (zeroM M) c HY)).
      exact (proj2 (environment_cons_head M ab ac an c cb cc cn c HCol) eq_refl).
    - exact HL. }
  destruct HI as (xb & xc & xn & rhs & HX & HRhs & GEx).
  destruct HRhs as (input & theta & HInput & HTheta & GRhs).
  assert (GInput:quotation_atom M false base a t (succM M base) input).
  { apply (replacement_skeleton_atom_values M (schema_env3 ra rb rc) xb xc xn (succM M base) t false 0 3 base a input).
    - exact (proj2 (environment_cons_head M yb yc yn base xb xc xn base HX) eq_refl).
    - change (environment_lookup M xb xc xn (succM M (succM M (succM M (zeroM M)))) a).
      apply (proj2 (environment_cons_tail M yb yc yn base xb xc xn (succM M (succM M (zeroM M))) a HX)).
      apply (proj2 (environment_cons_tail M cb cc cn y yb yc yn (succM M (zeroM M)) a HY)).
      apply (proj2 (environment_cons_tail M ab ac an c cb cc cn (zeroM M) a HCol)).
      exact (proj2 (environment_cons_head M eb ec en a ab ac an a HA) eq_refl).
    - exact HInput. }
  assert (GTheta:binary_matrix_quotation M phi eb ec en base y (succM M base) t theta).
  { apply (range_body_is_binary_matrix M phi rc bound eb ec en a c base y
      ab ac an cb cc cn yb yc yn xb xc xn (succM M base) t theta HB HC HA HCol HY HX).
    exact HTheta. }
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 1)) (t .: base .: fun _=>zeroM M)) as [dom GD].
  apply (proj1 (NamedLeibnizSteps.ns_atom_expression M _ false (CEvar 0) (CEvar 1) t base dom eq_refl eq_refl)) in GD.
  destruct (quotation_binary_total M SFAnd dom rhs) as [body GB].
  exists left,image,forward,backward;split;[exact GLeft|]. split.
  - exists input,theta,dom,rhs,body;split;[exact GInput|]. split;[exact GTheta|]. split;[exact GD|]. split;[exact GRhs|]. split;[exact GB|].
    exact (proj1 (quotation_guarded_exists_graph M base t rhs dom body image GD GB) GEx).
  - split;[exact HFor|]. split;assumption.
Qed.

Print Assumptions skeleton_quotation_functional.
Print Assumptions skeleton_quotation_total.
Print Assumptions replacement_pointwise_skeleton_data.

