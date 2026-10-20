(** Uniform actual native witness request with all selector maps and their
 reflection proofs internally generated. Parameter memberships are supplied
 by one literal internally finite source membership-block proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceFiniteCutoffShift
 SourceWitnessThetaRecipe SourceWitnessThetaInstances SourceWitnessAssignmentBounds SourceNativeWitnessRequest
 SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks
 SourceReflectedRequestLink SourceZFRProvability ContextCombination NumericalContexts NumericalSourceFull NumericalSubstitution.
Unset Implicit Arguments.
Theorem source_full_native_witness_request_total M domain phi theta n beta carrier p s t delta
 refl level block pY sY tY st gb gc gn k:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi(succM M(succM M n))->
 source_witness_theta_recipe M phi theta->context_bounded M gb gc gn k->
 coding_lt M beta k->coding_lt M carrier k->coding_lt M p k->coding_lt M s k->coding_lt M t k->
 (forall j,coding_lt M j n->coding_lt M(addM M j delta)k)->
 source_ordinary_reflection M domain(source_succ_iter M 4 n)theta beta refl->source_LL_instance M beta carrier level->
 source_membership_block M delta carrier n block->sf_relation M SFMember p carrier pY->
 sf_relation M SFMember s carrier sY->sf_relation M SFMember t carrier tY->sf_relation M SFMember s t st->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn level->source_full_prv M gb gc gn block->
 source_full_prv M gb gc gn pY->source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->
 exists mb mc matrix request nb nc nn ub uc un,
 source_witness_matrix_map M p delta mb mc /\
 numerical_substitution M phi mb mc(code_numeral M 2)(succM M delta)matrix /\
 source_reflected_request_recipe M domain carrier matrix request /\source_zfr_context M nb nc nn /\
 context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un request.
Proof.
 intros HD BP HTheta BC HB HY HPN HSN HTN HNames HR HL HBlock HPY HSY HTY HST PR PL PBlock PPY PSY PTY PST.
 pose proof(source_witness_theta_recipe_bound M phi theta n BP HTheta)as BTheta.
 destruct(source_witness_theta_diagonal_point_total M phi(succM M(succM M n))theta p s t delta BP HTheta)
  as(db&dc&pb&pc&mb&mc&diagonal&rawPoint&matrix&some&pp&stshift&diagonalHole&pointHole&
    HMapD&HMapP&HMapM&HSubD&HSubP&HSubM&HSome&HPP&HSTShift&HSelectorD&HSelectorP).
 pose proof(source_witness_diagonal_maps_bound M p delta db dc n k HMapD HPN HNames)as BMapD.
 pose proof(source_witness_point_maps_bound M p s t delta db dc pb pc(source_succ_iter M 4 n)k
  HMapD HMapP HPN HSN HTN BMapD)as BMapP.
 pose proof(source_full_witness_diagonal_members M p delta db dc n carrier block pY gb gc gn k
  HMapD BC HY HNames HBlock HPY PBlock PPY)as HMembers.
 destruct(source_full_native_witness_request M domain theta(source_succ_iter M 4 n)beta carrier p s t delta db dc pb pc
  diagonal rawPoint matrix some pp stshift diagonalHole pointHole refl level pY sY tY st gb gc gn k
  HD BTheta BC HB HY HMapD HMapP BMapD BMapP HSubD HSubP HSome HPP HSTShift HSelectorD HSelectorP
  HR HL HPY HSY HTY HST PR PL PPY PSY PTY PST HMembers)
  as(request&nb&nc&nn&ub&uc&un&HRequest&HNC&HU&PRequest).
 exists mb,mc,matrix,request,nb,nc,nn,ub,uc,un. repeat first[assumption|split].
Qed.
Print Assumptions source_full_native_witness_request_total.
