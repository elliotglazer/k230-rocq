(** The finite source-premise tuple of a one-pair attempt extension. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceRecursionPrimitiveRelations
 SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionSetOperations
 SourceRecursionSetOperationTransport SourceRecursionBinaryInstance SourceRecursionExtensionPoint.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_extension_inputs M phi o a N f q g z next p w A:=exists inj att mz sz appf adj op binary,
 A=[inj;att;mz;sz;appf;adj;op;binary] /\source_rec_injectivity M N inj /\source_rec_attempt M phi o a N f att /\
 sf_relation M SFMember z N mz /\source_rec_successor M z next sz /\source_rec_app M f z p appf /\source_rec_adjoin M f q g adj /\
 source_rec_ordered_pair M next w q op /\source_rec_binary M phi p w binary.
Theorem source_rec_extension_inputs_total M phi o a N f q g z next p w:exists A,source_rec_extension_inputs M phi o a N f q g z next p w A.
Proof.
 destruct(source_rec_injectivity_total M N)as(inj&HI).
 destruct(source_rec_attempt_total M phi o a N f)as(att&HT).
 destruct(sf_relation_total M SFMember z N)as(mz&HMZ).
 destruct(source_rec_successor_total M z next)as(sz&HSZ).
 destruct(source_rec_app_total M f z p)as(appf&HAF).
 destruct(source_rec_adjoin_total M f q g)as(adj&HA).
 destruct(source_rec_ordered_pair_total M next w q)as(op&HO).
 destruct(source_rec_binary_total M phi p w)as(binary&HG).
 exists[inj;att;mz;sz;appf;adj;op;binary],inj,att,mz,sz,appf,adj,op,binary. split;[reflexivity|]. auto 10.
Qed.
Theorem source_rec_extension_inputs_bounded M phi o a N f q g z next p w A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->source_rec_extension_inputs M phi o a N f q g z next p w A ->
 forall x,In x A ->source_bounded M x k.
Proof.
 intros BP BO BA BN BF BQ BG BZ BNext BP' BW(inj&att&mz&sz&appf&adj&op&binary&E&HI&HT&HMZ&HSZ&HAF&HA&HO&HG). subst A.
 intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
 - exact(source_rec_injectivity_bounded M N inj k BN HI).
 - exact(source_rec_attempt_bounded M phi o a N f att k BP BO BA BN BF HT).
 - exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
 - exact(source_rec_successor_bounded M z next sz k BZ BNext HSZ).
 - exact(source_rec_app_bounded M f z p appf k BF BZ BP' HAF).
 - exact(source_rec_adjoin_bounded M f q g adj k BF BQ BG HA).
 - exact(source_rec_ordered_pair_bounded M next w q op k BNext BW BQ HO).
 - exact(source_rec_binary_bounded M phi p w binary k BP BP' BW HG).
Qed.
Print Assumptions source_rec_extension_inputs_total.
Print Assumptions source_rec_extension_inputs_bounded.
