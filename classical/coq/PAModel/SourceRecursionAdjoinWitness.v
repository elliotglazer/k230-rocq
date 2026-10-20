(** A genuine predecessor witness survives adjoining a pair to its attempt. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceImplicationAllShift SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionBinaryInstance SourceRecursionAttemptStepShell SourceRecursionValuePairs
 SourceRecursionSetOperations SourceRecursionSetOperationTransport SourceRecursionAdjoinLeft
 SourceConditionalProofs SourceConditionalConjunctionLeft SourceConditionalQuantifiers SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_rec_transition_adjoin M phi f q g u v adj old new point law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->coding_lt M u k ->coding_lt M v k ->
 source_rec_adjoin M f q g adj ->source_rec_transition_witness M phi f u v old ->source_rec_transition_witness M phi g u v new ->
 sf_relation M SFImpl old new point ->sf_relation M SFImpl adj point law ->source_zfr_provable M law.
Proof.
 intros BP BF BQ BG BU BV HAdj HOld HNew HP HL.
 pose proof(source_rec_adjoin_bounded M f q g adj k BF BQ BG HAdj)as BAdj.
 pose proof(source_rec_transition_witness_bounded M phi f u v old k BP BF BU BV HOld)as BOld.
 pose proof(source_rec_transition_witness_bounded M phi g u v new k BP BG BU BV HNew)as BNew.
 destruct HOld as(oldApp&binary&body&HOApp&HBinary&HBody&HOldEx).
 destruct HNew as(newApp&binary'&body'&HNApp&HBinary'&HBody'&HNewEx).
 pose proof(source_rec_binary_functional M phi(zeroM M)(succM M v)binary' binary HBinary' HBinary)as E. subst binary'.
 pose proof(proj1(source_bounded_accept_unary M SFEx body old k(or_intror eq_refl)HOldEx)BOld)as BBody.
 pose proof(proj1(source_bounded_accept_unary M SFEx body' new k(or_intror eq_refl)HNewEx)BNew)as BBody'.
 destruct(proj1(source_bounded_accept_binary M SFAnd oldApp binary body(succM M k)(or_introl eq_refl)HBody)BBody)as[BOldApp BBinary].
 destruct(proj1(source_bounded_accept_binary M SFAnd newApp binary body'(succM M k)(or_introl eq_refl)HBody')BBody')as[BNewApp BBinary'].
 destruct(source_rec_adjoin_total M(succM M f)(succM M q)(succM M g))as(adj1&HAdj1).
 pose proof(source_rec_adjoin_shift M f q g adj adj1 HAdj HAdj1)as SAdj.
 pose proof(source_shift_bound M adj adj1 k BAdj SAdj)as BAdj1.
 assert(Head:source_conditional_implies M adj1 oldApp newApp).
 { intros map HM out HO. exact(source_zfr_rec_adjoin_left M(succM M f)(succM M q)(succM M g)(succM M u)(zeroM M)adj1 oldApp newApp map out HAdj1 HOApp HNApp HM HO). }
 pose proof(source_conditional_and_left M adj1 oldApp newApp binary body body'(succM M k)BAdj1 BOldApp BNewApp BBinary HBody HBody' Head)as Body.
 exact(source_conditional_implies_quantifier M SFEx adj adj1 body body' old new k(or_intror eq_refl)BAdj SAdj BBody BBody' HOldEx HNewEx Body point HP law HL).
Qed.
Print Assumptions source_zfr_rec_transition_adjoin.
