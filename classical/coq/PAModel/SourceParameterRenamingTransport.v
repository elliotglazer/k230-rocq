(** Renaming between finite parameter compilations via actual substitution. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceFiniteParameters SourceParameterTransport
 NumericalRenamingMaps NumericalRenaming RenamingSubstitution.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
Theorem source_parameter_renaming_transport {ff} M bound
 (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff):
 bounded bound phi ->forall names names' rho rho' b c n delta f g,
 (forall i x y,(i<bound)%nat ->code_relation M rho(names i)x ->code_relation M rho'(names' i)y ->
  renaming_lookup M b c n delta x y) ->
 code_relation M rho(source_parameter_expression names phi)f ->
 code_relation M rho'(source_parameter_expression names' phi)g ->numerical_renaming M f b c n delta g.
Proof.
 intros HB names names' rho rho' b c n delta f g HNames HF HG.
 apply(proj2(numerical_renaming_substitution M f b c n delta g)).
 apply(source_parameter_transport M bound phi HB names names' rho rho' b c n(addM M n delta)f g);[|exact HF|exact HG].
 intros i x y HI HX HY. apply(proj1(renaming_substitution_lookup M b c n delta x y)).
 exact(HNames i x y HI HX HY).
Qed.
Print Assumptions source_parameter_renaming_transport.
