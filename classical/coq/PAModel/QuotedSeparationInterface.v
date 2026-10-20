(** Corrected quoted-predicate Separation interface. Arbitrary raw predicates
    need not be invariant under deqv. This interface retains the actual source
    quotation and its parameter environment for the quotient transfer. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  NumericalEnvironments NumericalQuotation QuotationHygiene QuotationPayloads
  SetSchemaConstructors SourceBounded SchemaRenamingDescriptors SchemaImageReduction
  NumericalEquivalence FreshNames QuotationSchemaSkeleton QuotationFunctionality
  SeparationMatrixEnvironment DomainSeparationImage.
Unset Implicit Arguments.

Definition quoted_domain_separation_certificates M marker :=
  forall phi bound eb ec en a mb mc mn theta left right q,
  source_bounded M phi bound -> quotation_safe M eb ec en a (code_numeral M 1) ->
  environment_cons M eb ec en (succM M (succM M a)) mb mc mn ->
  numerical_quotation M phi mb mc mn (succM M (succM M (succM M a))) (code_numeral M 1) theta ->
  formula_fresh M theta a -> formula_fresh M theta (succM M a) ->
  quotation_atom M false (succM M (succM M a)) (succM M a)
    (code_numeral M 1) (succM M (succM M (succM M a))) left ->
  quotation_atom M false (succM M (succM M a)) a
    (code_numeral M 1) (succM M (succM M (succM M a))) right ->
  domain_separation_graph M a theta left right q -> numerical_implies M marker q.

Theorem separation_open_quoted_image_data M phi bound body axiom eb ec en a q :
  source_bounded M phi bound -> schema_renaming M SepBody phi body ->
  sf_separation_constructor M body axiom ->
  quotation_safe M eb ec en a (code_numeral M 1) ->
  numerical_quotation M axiom eb ec en a (code_numeral M 1) q ->
  exists theta left right mb mc mn,
    environment_cons M eb ec en (succM M (succM M a)) mb mc mn /\
    numerical_quotation M phi mb mc mn (succM M (succM M (succM M a))) (code_numeral M 1) theta /\
    formula_fresh M theta a /\ formula_fresh M theta (succM M a) /\
    quotation_atom M false (succM M (succM M a)) (succM M a)
      (code_numeral M 1) (succM M (succM M (succM M a))) left /\
    quotation_atom M false (succM M (succM M a)) a
      (code_numeral M 1) (succM M (succM M (succM M a))) right /\
    domain_separation_graph M a theta left right q.
Proof.
  intros HBound HRen HConstruct HSafe HQ.
  apply (proj2 (separation_quotation_skeleton M body axiom eb ec en a (code_numeral M 1) q HConstruct)) in HQ.
  cbn [separation_skeleton skeleton_iff skeleton_and skeleton_impl skeleton_quotation] in HQ.
  destruct HQ as [ab [ac [an [exb [HA [HQ HQOut]]]]]].
  destruct HQ as [bb [bc [bn [allx [HB [HQ HBOut]]]]]].
  destruct HQ as [xb [xc [xn [iffcode [HX [HQ HXOut]]]]]].
  destruct HQ as [forward [backward [HFwd [HBwd HIff]]]].
  destruct HFwd as [left [rhs [HLeft [HRhs HForward]]]].
  destruct HRhs as [right [theta [HRight [HTheta HRhs]]]].
  destruct HBwd as [rhs' [left' [HRhs' [HLeft' HBackward]]]].
  destruct HRhs' as [right' [theta' [HRight' [HTheta' HRhs']]]].
  assert (ETheta : theta'=theta).
  { exact (numerical_quotation_functional M body xb xc xn
      (succM M (succM M (succM M a))) (code_numeral M 1) theta' theta HTheta' HTheta). }
  subst theta'.
  assert (LX : environment_lookup M xb xc xn (code_numeral M 0) (succM M (succM M a))).
  { apply (proj2 (environment_cons_head M bb bc bn (succM M (succM M a)) xb xc xn _ HX)). reflexivity. }
  assert (LB : environment_lookup M xb xc xn (code_numeral M 1) (succM M a)).
  { apply (proj2 (environment_cons_tail M bb bc bn (succM M (succM M a)) xb xc xn (zeroM M) _ HX)).
    apply (proj2 (environment_cons_head M ab ac an (succM M a) bb bc bn _ HB)). reflexivity. }
  assert (LA : environment_lookup M xb xc xn (code_numeral M 2) a).
  { apply (proj2 (environment_cons_tail M bb bc bn (succM M (succM M a)) xb xc xn (code_numeral M 1) _ HX)).
    apply (proj2 (environment_cons_tail M ab ac an (succM M a) bb bc bn (zeroM M) _ HB)).
    apply (proj2 (environment_cons_head M eb ec en a ab ac an _ HA)). reflexivity. }
  apply (separation_skeleton_atom_values M (fun _=>body) xb xc xn
    (succM M (succM M (succM M a))) (code_numeral M 1) false 0 1 _ _ left LX LB) in HLeft.
  apply (separation_skeleton_atom_values M (fun _=>body) xb xc xn
    (succM M (succM M (succM M a))) (code_numeral M 1) false 0 1 _ _ left' LX LB) in HLeft'.
  apply (separation_skeleton_atom_values M (fun _=>body) xb xc xn
    (succM M (succM M (succM M a))) (code_numeral M 1) false 0 2 _ _ right LX LA) in HRight.
  apply (separation_skeleton_atom_values M (fun _=>body) xb xc xn
    (succM M (succM M (succM M a))) (code_numeral M 1) false 0 2 _ _ right' LX LA) in HRight'.
  assert (left'=left) by exact (quotation_atom_functional M false _ _ _ _ _ _ HLeft' HLeft).
  assert (right'=right) by exact (quotation_atom_functional M false _ _ _ _ _ _ HRight' HRight).
  subst left' right'.
  assert (rhs'=rhs) by exact (quotation_binary_functional M SFAnd right theta rhs' rhs HRhs' HRhs).
  subst rhs'.
  destruct (environment_cons_total M eb ec en (succM M (succM M a))) as [mb [mc [mn HM]]].
  destruct (numerical_quotation_total M phi mb mc mn
    (succM M (succM M (succM M a))) (code_numeral M 1)) as [original HOriginal].
  assert (EOriginal : original=theta).
  { exact (separation_matrix_quotation M phi body bound eb ec en a (succM M a) (succM M (succM M a))
      ab ac an bb bc bn xb xc xn mb mc mn (succM M (succM M (succM M a)))
      (code_numeral M 1) original theta HBound HRen HA HB HX HM HOriginal HTheta). }
  subst original.
  destruct (separation_matrix_fresh M phi eb ec en a mb mc mn theta HSafe HM HOriginal) as [HFa HFb].
  exists theta,left,right,mb,mc,mn. split;[exact HM|]. split;[exact HOriginal|].
  split;[exact HFa|]. split;[exact HFb|].
  split;[exact HLeft|]. split;[exact HRight|].
  exists rhs,forward,backward,iffcode,allx,exb. repeat split;assumption.
Qed.

Theorem open_separation_images_from_quoted_domain M marker :
  quoted_domain_separation_certificates M marker -> open_separation_images M marker.
Proof.
  intros HSep phi count body axiom HBound HRen HC eb ec en fresh q HSafe HQ.
  destruct (separation_open_quoted_image_data M phi (succM M count) body axiom eb ec en fresh q
    HBound HRen HC HSafe HQ) as [theta [left [right [mb [mc [mn [HM [HTheta [HFa [HFb [HL [HR HG]]]]]]]]]]]].
  exact (HSep phi (succM M count) eb ec en fresh mb mc mn theta left right q
    HBound HSafe HM HTheta HFa HFb HL HR HG).
Qed.

Print Assumptions separation_open_quoted_image_data.
Print Assumptions open_separation_images_from_quoted_domain.
