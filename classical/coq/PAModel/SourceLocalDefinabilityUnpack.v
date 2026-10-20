(** Exact finite Def0 unpacking, with model-valued names for both witnesses.
    The finite library proof is consumed in the same genuine closed context. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterNamedBinder SourceParameterGraphs
 SourceNamedQuantifierRules SourceLocalDefinabilityFixed SourceLocalDefinabilityContext
 SourceDerivedRules SourceProofWeakening SourceEnvironmentCarrierClosure OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_base Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_local_def_predicate:sf_form:=isolated_formula
 (OldZFC.Z_cl.Def0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Definition source_local_def_predicate_expression:=source_parameter_expression(source_finite_parameter_names 2)source_local_def_predicate.
Definition source_local_unpack_content:sf_form:=isolated_formula
 (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Conj
  (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Conj
   (OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 1))
   (OldZFC.Z_cl.Cl(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)))
  (@OC.quant OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.All
   (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
    (@OC.atom OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OS.elem
     (Vector.cons _ (@OC.var OB.sig_empty 0) _ (Vector.cons _ (@OC.var OB.sig_empty 1) _ (Vector.nil _))))
    (@OC.bin OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Impl
     (OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 3))
     (@OC.atom OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators OC.falsity_on OS.elem
      (Vector.cons _ (@OC.var OB.sig_empty 0) _ (Vector.cons _ (@OC.var OB.sig_empty 4) _ (Vector.nil _)))))))).
Definition source_local_unpack_middle:sf_form:=@Undecidability.FOL.Syntax.Core.quant Undecidability.FOL.Syntax.BinSig.sig_empty Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig Undecidability.FOL.Syntax.Core.FullSyntax.full_operators Undecidability.FOL.Syntax.Core.falsity_on Undecidability.FOL.Syntax.Core.FullSyntax.Ex source_local_unpack_content.
Definition source_local_unpack_exists:sf_form:=@Undecidability.FOL.Syntax.Core.quant Undecidability.FOL.Syntax.BinSig.sig_empty Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig Undecidability.FOL.Syntax.Core.FullSyntax.full_operators Undecidability.FOL.Syntax.Core.falsity_on Undecidability.FOL.Syntax.Core.FullSyntax.Ex source_local_unpack_middle.
Definition local_def_names {A}(carrier definables:A)i:=match i with 0=>carrier|_=>definables end.
Definition local_unpack_middle_names {A}(successor carrier definables:A)i:=match i with 0=>successor|1=>carrier|_=>definables end.
Definition local_unpack_content_names {A}(closure successor carrier definables:A)i:=match i with 0=>closure|1=>successor|2=>carrier|_=>definables end.
Lemma source_local_unpack_content_bound:bounded 4 source_local_unpack_content.
Proof. unfold source_local_unpack_content. apply(@isolated_bounded OC.falsity_on 4),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma source_local_unpack_middle_bound:bounded 3 source_local_unpack_middle.
Proof. constructor. exact source_local_unpack_content_bound. Qed.
Lemma source_local_unpack_expression_shell:source_local_def_unpack_expression=
 E_sf SFImpl source_local_def_predicate_expression
 (source_parameter_expression(source_finite_parameter_names 2)source_local_unpack_exists).
Proof. reflexivity. Qed.
Theorem source_local_def_unpack_named_graph M carrier definables successor closure content middle out:
 closure<>successor ->closure<>carrier ->closure<>definables ->successor<>carrier ->successor<>definables ->
 code_relation M(local_unpack_content_names closure successor carrier definables)
  (source_parameter_expression(source_finite_parameter_names 4)source_local_unpack_content)content ->
 code_relation M(local_unpack_middle_names successor carrier definables)
  (source_parameter_expression(source_finite_parameter_names 3)source_local_unpack_middle)middle ->
 code_relation M(local_def_names carrier definables)
  (source_parameter_expression(source_finite_parameter_names 2)source_local_unpack_exists)out ->
 source_named_quantifier M false closure content middle /\source_named_quantifier M false successor middle out.
Proof.
 intros CS CA CD SA SD HContent HMiddle HOut. split.
 - apply(source_finite_parameter_named_binder M 3 source_local_unpack_content
    (local_unpack_middle_names successor carrier definables)closure content middle false).
   + exact source_local_unpack_content_bound.
   + intros[|[|[|i]]]HI;try lia;cbn[local_unpack_middle_names];assumption.
   + exact HContent.
   + exact HMiddle.
 - apply(source_finite_parameter_named_binder M 2 source_local_unpack_middle
    (local_def_names carrier definables)successor middle out false).
   + exact source_local_unpack_middle_bound.
   + intros[|[|i]]HI;try lia;cbn[local_def_names];assumption.
   + exact HMiddle.
   + exact HOut.
Qed.
Theorem source_full_local_def_unpack M fb fc fn gb gc gn carrier definables predicate out law k:
 source_local_fixed_context M fb fc fn ->context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 code_relation M(local_def_names carrier definables)source_local_def_predicate_expression predicate ->
 code_relation M(local_def_names carrier definables)
  (source_parameter_expression(source_finite_parameter_names 2)source_local_unpack_exists)out ->
 sf_relation M SFImpl predicate out law ->source_full_prv M gb gc gn predicate ->source_full_prv M gb gc gn out.
Proof.
 intros HFixed HIncluded BC HDef HOut HLaw PDef.
 assert(HGraph:code_relation M(local_def_names carrier definables)source_local_def_unpack_expression law).
 { rewrite source_local_unpack_expression_shell. exact(environment_carrier_code_join M _ SFImpl _ _ predicate out law HDef HOut HLaw). }
 pose proof(source_full_local_fixed_instance M fb fc fn 1(local_def_names carrier definables)law HFixed ltac:(lia)HGraph)as PLaw.
 pose proof(source_full_prv_weaken_bounded M fb fc fn gb gc gn law k PLaw HIncluded BC)as PLaw'.
 exact(source_full_modus_ponens M gb gc gn predicate out law HLaw PLaw' PDef).
Qed.
Print Assumptions source_local_unpack_expression_shell.
Print Assumptions source_local_def_unpack_named_graph.
Print Assumptions source_full_local_def_unpack.
