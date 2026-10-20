(** The exact ordinary background of RR functionality, with checked shifts. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceQuantifierRules
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionInductionGraphs SourceRecursionInductionBounds
 SourceRecursionInductionShift SourceRecursionInductionTransport SourceRecursionAtomicShift.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_rec_rr_background M phi o N A:=exists funlaw totality induction member,
 A=[funlaw;totality;induction;member] /\source_rec_functionality M phi funlaw /\source_rec_totality M N totality /\
 source_rec_induction M o N induction /\sf_relation M SFMember o N member.
Theorem source_rec_rr_background_total M phi o N:exists A,source_rec_rr_background M phi o N A.
Proof.
 destruct(source_rec_functionality_total M phi)as(funlaw&HF).
 destruct(source_rec_totality_total M N)as(totality&HT).
 destruct(source_rec_induction_total M o N)as(induction&HI).
 destruct(sf_relation_total M SFMember o N)as(member&HM).
 exists[funlaw;totality;induction;member],funlaw,totality,induction,member. auto.
Qed.
Theorem source_rec_rr_background_bounded M phi o N A k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M N k ->source_rec_rr_background M phi o N A ->forall x,In x A ->source_bounded M x k.
Proof.
 intros BP BO BN(funlaw&totality&induction&member&E&HF&HT&HI&HM). subst A. intros x[<-|[<-|[<-|[<-|[]]]]].
 - exact(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HF)(coding_zero_lt_succ M k)).
 - exact(source_rec_totality_bounded M N totality k BN HT).
 - exact(source_rec_induction_bounded M o N induction k BO BN HI).
 - exact(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN)).
Qed.
Theorem source_rec_rr_background_shift M phi o N A AS:
 source_bounded M phi(code_numeral M 2) ->source_rec_rr_background M phi o N A ->source_rec_rr_background M phi(succM M o)(succM M N)AS ->Forall2(source_formula_shift M)A AS.
Proof.
 intros BP(funlaw&totality&induction&member&E&HF&HT&HI&HM)(funlawS&totalityS&inductionS&memberS&ES&HFS&HTS&HIS&HMS). subst A AS.
 destruct HF as(ra&rb&HRA&HRB&HFun). destruct HFS as(raS&rbS&HRAS&HRBS&HFunS).
 pose proof(SchemaRenamingDescriptors.schema_renaming_functional M SchemaRenamingDescriptors.RepA phi raS ra HRAS HRA)as E. subst raS.
 pose proof(SchemaRenamingDescriptors.schema_renaming_functional M SchemaRenamingDescriptors.RepB phi rbS rb HRBS HRB)as E. subst rbS.
 pose proof(code_relation_functional M _ _ funlawS funlaw HFunS HFun)as E. subst funlawS.
 assert(HF:source_rec_functionality M phi funlaw)by(exists ra,rb;auto).
 constructor;[exact(source_rec_functionality_shift M phi funlaw BP HF)|].
 constructor;[exact(source_rec_totality_shift M N totality totalityS HT HTS)|].
 constructor;[exact(source_rec_induction_shift M o N induction inductionS HI HIS)|].
 constructor;[exact(source_rec_member_shift M o N member memberS HM HMS)|constructor].
Qed.
Print Assumptions source_rec_rr_background_total.
Print Assumptions source_rec_rr_background_bounded.
Print Assumptions source_rec_rr_background_shift.
