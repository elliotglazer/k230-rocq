(** A fixed seven-premise tuple for genuine ExA successor construction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionAttemptTransport
 SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionPrimitiveShifts SourceRecursionNonzeroTransport
 SourceRecursionBinaryInstance SourceRecursionShiftGraphs SourceRecursionAtomicShift SourceRecursionExtensionInputShift.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_exa_step_inputs M phi o a N f z next p w A:=exists nonzero inj att mz sz appf binary,
 A=[nonzero;inj;att;mz;sz;appf;binary] /\source_rec_nonzero M o N nonzero /\source_rec_injectivity M N inj /\source_rec_attempt M phi o a N f att /\
 sf_relation M SFMember z N mz /\source_rec_successor M z next sz /\source_rec_app M f z p appf /\source_rec_binary M phi p w binary.
Theorem source_rec_exa_step_inputs_total M phi o a N f z next p w:exists A,source_rec_exa_step_inputs M phi o a N f z next p w A.
Proof.
 destruct(source_rec_nonzero_total M o N)as(nonzero&HNZ).
 destruct(source_rec_injectivity_total M N)as(inj&HI).
 destruct(source_rec_attempt_total M phi o a N f)as(att&HT).
 destruct(sf_relation_total M SFMember z N)as(mz&HMZ).
 destruct(source_rec_successor_total M z next)as(sz&HSZ).
 destruct(source_rec_app_total M f z p)as(appf&HAF).
 destruct(source_rec_binary_total M phi p w)as(binary&HG).
 exists[nonzero;inj;att;mz;sz;appf;binary],nonzero,inj,att,mz,sz,appf,binary. split;[reflexivity|]. auto 10.
Qed.
Theorem source_rec_exa_step_inputs_bounded M phi o a N f z next p w A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->
 coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->source_rec_exa_step_inputs M phi o a N f z next p w A ->
 forall x,In x A ->source_bounded M x k.
Proof.
 intros BP BO BA BN BF BZ BNext BP' BW(nonzero&inj&att&mz&sz&appf&binary&E&HNZ&HI&HT&HMZ&HSZ&HAF&HG). subst A.
 intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
 - exact(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ).
 - exact(source_rec_injectivity_bounded M N inj k BN HI).
 - exact(source_rec_attempt_bounded M phi o a N f att k BP BO BA BN BF HT).
 - exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
 - exact(source_rec_successor_bounded M z next sz k BZ BNext HSZ).
 - exact(source_rec_app_bounded M f z p appf k BF BZ BP' HAF).
 - exact(source_rec_binary_bounded M phi p w binary k BP BP' BW HG).
Qed.
Theorem source_rec_exa_step_inputs_shift M phi o a N f z next p w A AS:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_step_inputs M phi o a N f z next p w A ->
 source_rec_exa_step_inputs M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M z)(succM M next)(succM M p)(succM M w)AS ->
 Forall2(source_formula_shift M)A AS.
Proof.
 intros BP(nonzero&inj&att&mz&sz&appf&binary&E&HNZ&HI&HT&HMZ&HSZ&HAF&HG)
  (nonzero'&inj'&att'&mz'&sz'&appf'&binary'&E'&HNZ'&HI'&HT'&HMZ'&HSZ'&HAF'&HG'). subst A AS.
 constructor;[exact(source_rec_nonzero_shift M o N nonzero nonzero' HNZ HNZ')|].
 constructor;[exact(source_rec_injectivity_shift M N inj inj' HI HI')|].
 constructor;[exact(source_rec_attempt_shift M phi o a N f att att' BP HT HT')|].
 constructor;[exact(source_rec_member_shift M z N mz mz' HMZ HMZ')|].
 constructor;[exact(source_rec_successor_shift M z next sz sz' HSZ HSZ')|].
 constructor;[exact(source_rec_app_shift M f z p appf appf' HAF HAF')|].
 constructor;[exact(source_rec_binary_shift M phi p w binary binary' BP HG HG')|constructor].
Qed.
Print Assumptions source_rec_exa_step_inputs_total.
Print Assumptions source_rec_exa_step_inputs_bounded.
Print Assumptions source_rec_exa_step_inputs_shift.
