(** Full internally-many assignment closure of the double-difference law.
    The Op2 conditions remain outside Dn, including their extra set names.
    Only literal syntax graphs and bounds are inputs. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram SourceRepresentationDifferencePoints
 SourceRepresentationDifferenceLaw SourceRepresentationPadding SourceDn SourceDnPaddedBinaryMap
 SourceDescriptorProvability SourceDescriptorClosure.
Unset Implicit Arguments.
Theorem source_descriptor_double_difference_dn M T count rho k operation1 operation2 condition padded
 point1 point2 target rep1 rep2 repTarget innerPoint pointLaw pointProof innerRep repLaw result :
 (forall i,(i<4)%nat ->coding_lt M(rho i)(addM M count(succM M(succM M k)))) ->
 source_bounded M(rho 4)(succM M(addM M count(succM M(succM M k)))) ->
 source_bounded M(rho 5)(succM M(addM M count(succM M(succM M k)))) ->
 source_bounded M(rho 6)(succM M(addM M count(succM M(succM M k)))) ->
 source_bounded M condition(succM M(succM M k)) ->
 source_bounded M padded(addM M count(succM M(succM M k))) ->
 source_bounded M point1(addM M count(succM M(succM M k))) ->
 source_bounded M point2(addM M count(succM M(succM M k))) ->
 source_bounded M target(addM M count(succM M(succM M k))) ->
 source_representation_padding M count condition padded ->
 code_relation M rho E_double_difference_first_operation operation1 ->
 code_relation M rho E_double_difference_second_operation operation2 ->
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4)))) point1 ->
 code_relation M rho(E_double_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5)))) point2 ->
 code_relation M rho(E_double_difference_all double_difference_conclusion)target ->
 sf_relation M SFAnd operation1 operation2 padded ->
 sf_relation M SFImpl point2 target innerPoint ->sf_relation M SFImpl point1 innerPoint pointLaw ->
 sf_relation M SFImpl padded pointLaw pointProof ->
 source_dn M count point1 rep1 ->source_dn M count point2 rep2 ->source_dn M count target repTarget ->
 sf_relation M SFImpl rep2 repTarget innerRep ->sf_relation M SFImpl rep1 innerRep repLaw ->
 sf_relation M SFImpl condition repLaw result ->source_descriptor_provable M T result.
Proof.
 intros HNames B4 B5 B6 BCond BPad BP1 BP2 BT HPad HO1 HO2 HP1 HP2 HT HAnd HIP HPL HPP
   HD1 HD2 HDT HIR HRL HResult.
 apply(source_descriptor_dn_padded_binary_map M T count condition padded point1 point2 target rep1 rep2 repTarget
   innerPoint pointLaw pointProof innerRep repLaw result k BCond BP1 BP2 BT HPad HD1 HD2 HDT HIP HPL HPP HIR HRL HResult).
 apply source_descriptor_provable_from_empty.
 exact(source_double_difference_point_law_empty M rho(addM M count(succM M(succM M k)))
   operation1 operation2 padded point1 point2 target innerPoint pointLaw pointProof
   HNames B4 B5 B6 BPad BP1 BP2 BT HO1 HO2 HP1 HP2 HT HAnd HIP HPL HPP).
Qed.
Print Assumptions source_descriptor_double_difference_dn.
