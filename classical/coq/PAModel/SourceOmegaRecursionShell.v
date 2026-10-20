(** Exact shared predicate projections of the fixed omega recursion body. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceOmegaRecursionOld SourceOmegaRecursionFixed OldNamedSyntaxBridge
  SourceFiniteParameters SourceFiniteParameterIdentity SourceRecursionInductionGraphs
  SourceRecursionStructureGraphs SchemaConstructorBounds QuotationSchemaSkeleton SourcePropositionalRebase.
From OldZF Require Std_setinf Std_setrec.
Unset Implicit Arguments.
Local Opaque code_numeral.

Theorem source_omega_recursion_body_shell M:
 exists member total injective nonzero inductive tail1 tail2 tail3,
 sf_relation M SFMember(code_numeral M 0)(code_numeral M 1)member /\
 source_rec_totality M(code_numeral M 1)total /\
 source_rec_injectivity M(code_numeral M 1)injective /\
 source_rec_nonzero M(code_numeral M 0)(code_numeral M 1)nonzero /\
 source_rec_induction M(code_numeral M 0)(code_numeral M 1)inductive /\
 sf_relation M SFAnd nonzero inductive tail3 /\
 sf_relation M SFAnd injective tail3 tail2 /\
 sf_relation M SFAnd total tail2 tail1 /\
 sf_relation M SFAnd member tail1(source_omega_recursion_body_code M).
Proof.
 pose proof(source_parameter_identity_numeral M source_omega_recursion_body)as HG.
 change(code_relation M(fun _=>zeroM M)
  (E_sf SFAnd(E_sf SFMember(CEconst 0)(CEconst 1))
   (E_sf SFAnd(source_parameter_expression CEconst
     (isolated_formula(OldZF.Std_setrec.STot OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 1))))
    (E_sf SFAnd(source_parameter_expression CEconst
     (isolated_formula(OldZF.Std_setrec.SInj OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 1))))
     (E_sf SFAnd(source_parameter_expression CEconst
      (isolated_formula(OldZF.Std_setrec.SNz OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
      (source_parameter_expression CEconst
      (isolated_formula(OldZF.Std_setrec.SInd OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))))))
  (source_omega_recursion_body_code M))in HG.
 destruct(schema_expression_split M _ SFAnd _ _ _ HG)as(member&tail1&HM&HT1&HOuter).
 destruct(schema_expression_split M _ SFAnd _ _ _ HT1)as(total&tail2&HT&HT2&HAnd1).
 destruct(schema_expression_split M _ SFAnd _ _ _ HT2)as(injective&tail3&HI&HT3&HAnd2).
 destruct(schema_expression_split M _ SFAnd _ _ _ HT3)as(nonzero&inductive&HN&HD&HAnd3).
 exists member,total,injective,nonzero,inductive,tail1,tail2,tail3.
 split.
 - exact(proj1(schema_expression_graph M(fun _=>zeroM M)SFMember(CEconst 0)(CEconst 1)(code_numeral M 0)(code_numeral M 1)member eq_refl eq_refl)HM).
 - split.
   + exact(source_parameter_rec_totality M CEconst(fun _=>zeroM M)1(code_numeral M 1)total eq_refl HT).
   + split.
     * exact(source_parameter_rec_injectivity M CEconst(fun _=>zeroM M)1(code_numeral M 1)injective eq_refl HI).
     * split.
       -- exact(source_parameter_rec_nonzero M CEconst(fun _=>zeroM M)0 1(code_numeral M 0)(code_numeral M 1)nonzero eq_refl eq_refl HN).
       -- split.
          ++ exact(source_parameter_rec_induction M CEconst(fun _=>zeroM M)0 1(code_numeral M 0)(code_numeral M 1)inductive eq_refl eq_refl HD).
          ++ repeat split;assumption.
Qed.
Print Assumptions source_omega_recursion_body_shell.
