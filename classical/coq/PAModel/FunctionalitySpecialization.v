(** The three quantifiers of source Replacement functionality can be
    instantiated at arbitrary model elements, with one common quote base. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeDescent
  ProofTemplates SetFormulaCodes SetSchemaConstructors NumericalEnvironments
  NumericalQuotation QuotationHygiene QuotationPayloads QuotationFunctionality
  QuotationSchemaSkeleton StableContextSupport SourceBounded SchemaRenamingDescriptors
  ReplacementMatrixQuotation ReplacementMatrixCongruence DomainReplacementImage
  ArbitraryWitnessQuotation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition functionality_matrix_skeleton :=
  skeleton_impl (SkeletonHole 0) (skeleton_impl (SkeletonHole 1) (SkeletonAtom true 1 0)).

Theorem stable_functionality_skeleton_specialization M cb cc cn sources
    eb ec en xb xc xn yb yc yn zb zc zn oldbase fresh domain x y z
    all result dx dy dz :
  quotation_safe M eb ec en oldbase domain -> quotation_safe M eb ec en fresh domain ->
  coding_lt M x fresh -> coding_lt M y fresh -> coding_lt M z fresh ->
  environment_cons M eb ec en x xb xc xn ->
  environment_cons M xb xc xn y yb yc yn ->
  environment_cons M yb yc yn z zb zc zn ->
  skeleton_quotation M functionality_skeleton sources eb ec en oldbase domain all ->
  skeleton_quotation M functionality_matrix_skeleton sources zb zc zn fresh domain result ->
  membership_graph M domain x dx -> membership_graph M domain y dy -> membership_graph M domain z dz ->
  stable_context_support M cb cc cn all -> stable_context_support M cb cc cn dx ->
  stable_context_support M cb cc cn dy -> stable_context_support M cb cc cn dz ->
  stable_context_support M cb cc cn result.
Proof.
  intros HOld HFresh HX HY HZ CX CY CZ HAll HResult HDX HDY HDZ PAll PX PY PZ.
  assert (HSX : quotation_safe M xb xc xn fresh domain).
  { split;[exact (proj1 HFresh)|].
    exact (replacement_environment_push_below M eb ec en x xb xc xn fresh
      (proj2 HFresh) HX CX). }
  assert (HSY : quotation_safe M yb yc yn fresh domain).
  { split;[exact (proj1 HFresh)|].
    exact (replacement_environment_push_below M xb xc xn y yb yc yn fresh
      (proj2 HSX) HY CY). }
  destruct (skeleton_quotation_total M
    (SkeletonQuantifier true (SkeletonQuantifier true functionality_matrix_skeleton))
    sources xb xc xn fresh domain) as [qX HQX].
  destruct (skeleton_quotation_total M (SkeletonQuantifier true functionality_matrix_skeleton)
    sources yb yc yn fresh domain) as [qY HQY].
  assert (PQX : stable_context_support M cb cc cn qX).
  { exact (stable_skeleton_all_arbitrary_witness M cb cc cn
      (SkeletonQuantifier true (SkeletonQuantifier true functionality_matrix_skeleton)) sources
      eb ec en xb xc xn oldbase fresh domain x all qX dx
      HOld HFresh HX CX HAll HQX HDX PAll PX). }
  assert (PQY : stable_context_support M cb cc cn qY).
  { exact (stable_skeleton_all_arbitrary_witness M cb cc cn
      (SkeletonQuantifier true functionality_matrix_skeleton) sources
      xb xc xn yb yc yn fresh fresh domain y qX qY dy
      HSX HSX HY CY HQX HQY HDY PQX PY). }
  exact (stable_skeleton_all_arbitrary_witness M cb cc cn functionality_matrix_skeleton sources
    yb yc yn zb zc zn fresh fresh domain z qY result dz
    HSY HSY HZ CZ HQY HResult HDZ PQY PZ).
Qed.

Theorem stable_replacement_functionality_specialization M cb cc cn phi bound a b source
    eb ec en oldbase fresh domain x y z all thetaXY thetaXZ eqYZ inner result dx dy dz :
  source_bounded M phi bound ->
  schema_renaming M RepA phi a -> schema_renaming M RepB phi b ->
  code_relation M (a .: b .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) source ->
  quotation_safe M eb ec en oldbase domain -> quotation_safe M eb ec en fresh domain ->
  coding_lt M x fresh -> coding_lt M y fresh -> coding_lt M z fresh ->
  numerical_quotation M source eb ec en oldbase domain all ->
  binary_matrix_quotation M phi eb ec en x y fresh domain thetaXY ->
  binary_matrix_quotation M phi eb ec en x z fresh domain thetaXZ ->
  quotation_atom M true y z domain fresh eqYZ ->
  quotation_binary M SFImpl thetaXZ eqYZ inner -> quotation_binary M SFImpl thetaXY inner result ->
  membership_graph M domain x dx -> membership_graph M domain y dy -> membership_graph M domain z dz ->
  stable_context_support M cb cc cn all -> stable_context_support M cb cc cn dx ->
  stable_context_support M cb cc cn dy -> stable_context_support M cb cc cn dz ->
  stable_context_support M cb cc cn result.
Proof.
  intros HBound HA HB HSource HOld HFresh HX HY HZ HAll HXY HXZ HEq HInner HResult
    HDX HDY HDZ PAll PX PY PZ.
  destruct (environment_cons_total M eb ec en x) as [xb [xc [xn CX]]].
  destruct (environment_cons_total M xb xc xn y) as [yb [yc [yn CY]]].
  destruct (environment_cons_total M yb yc yn z) as [zb [zc [zn CZ]]].
  set (sources:=a .: b .: fun _=>zeroM M).
  assert (QS : skeleton_quotation M functionality_skeleton sources eb ec en oldbase domain all).
  { exact (proj2 (skeleton_quotation_correct M functionality_skeleton sources source HSource
      eb ec en oldbase domain all) HAll). }
  destruct (skeleton_quotation_total M functionality_matrix_skeleton sources
    zb zc zn fresh domain) as [point HPoint].
  assert (PPoint : stable_context_support M cb cc cn point).
  { exact (stable_functionality_skeleton_specialization M cb cc cn sources
      eb ec en xb xc xn yb yc yn zb zc zn oldbase fresh domain x y z all point dx dy dz
      HOld HFresh HX HY HZ CX CY CZ QS HPoint HDX HDY HDZ PAll PX PY PZ). }
  cbn [functionality_matrix_skeleton skeleton_impl skeleton_quotation sources] in HPoint.
  destruct HPoint as [thetaA [impB [HThetaA [HRest HImpA]]]].
  destruct HRest as [thetaB [eq [HThetaB [HE HImpB]]]].
  assert (EA : thetaA=thetaXY).
  { apply (binary_matrix_quotation_functional M phi eb ec en x y fresh domain thetaA thetaXY).
    - exact (functionality_body_is_binary_matrix M RepA phi a bound eb ec en x y z
        xb xc xn yb yc yn zb zc zn fresh domain thetaA
        (or_introl eq_refl) HBound HA CX CY CZ HThetaA).
    - exact HXY. }
  assert (EB : thetaB=thetaXZ).
  { apply (binary_matrix_quotation_functional M phi eb ec en x z fresh domain thetaB thetaXZ).
    - exact (functionality_body_is_binary_matrix M RepB phi b bound eb ec en x y z
        xb xc xn yb yc yn zb zc zn fresh domain thetaB
        (or_intror eq_refl) HBound HB CX CY CZ HThetaB).
    - exact HXZ. }
  assert (LY : environment_lookup M zb zc zn (code_numeral M 1) y).
  { apply (proj2 (environment_cons_tail M yb yc yn z zb zc zn (zeroM M) y CZ)).
    apply (proj2 (environment_cons_head M xb xc xn y yb yc yn y CY)). reflexivity. }
  assert (LZ : environment_lookup M zb zc zn (code_numeral M 0) z).
  { apply (proj2 (environment_cons_head M yb yc yn z zb zc zn z CZ)). reflexivity. }
  apply (replacement_skeleton_atom_values M sources zb zc zn fresh domain true 1 0 y z eq LY LZ) in HE.
  assert (EE : eq=eqYZ) by exact (quotation_atom_functional M true y z domain fresh eq eqYZ HE HEq).
  subst thetaA thetaB eq.
  assert (EI : impB=inner) by exact (quotation_binary_functional M SFImpl thetaXZ eqYZ impB inner HImpB HInner).
  subst impB.
  assert (ER : point=result) by exact (quotation_binary_functional M SFImpl thetaXY inner point result HImpA HResult).
  now subst point.
Qed.

Print Assumptions stable_functionality_skeleton_specialization.
Print Assumptions stable_replacement_functionality_specialization.
