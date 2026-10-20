(** Literal embedding of an actual fragment derivation in full natural deduction. *)
From PAModel Require Import FullFragmentSyntax.
From Undecidability.FOL.Syntax Require Import Core.
From Undecidability.FOL.Deduction Require Import FullNDFacts.
From Undecidability.FOL.Deduction Require FragmentND.
From Stdlib Require Import Lists.List.
Import ListNotations.
Set Implicit Arguments.
Section ProofEmbedding.
Context {F:funcs_signature}{P:preds_signature}.
Lemma fragment_full_context_substitution {ff}(A:list(@form F P FragmentSyntax.frag_operators ff))sigma:
 List.map fragment_to_full(List.map(subst_form sigma)A)=
 List.map(subst_form sigma)(List.map fragment_to_full A).
Proof.
 rewrite !List.map_map. apply List.map_ext. intro phi. apply fragment_to_full_substitution.
Qed.
Theorem fragment_full_proof {ff}{p} A phi:
 @FragmentND.prv F P ff p A phi ->
 @FullND.prv F P falsity_on p(List.map fragment_to_full A)(fragment_to_full phi).
Proof.
 intro H. induction H;cbn.
 -now apply FullND.II.
 -eapply FullND.IE; eassumption.
 -apply FullND.AllI. now rewrite <-fragment_full_context_substitution.
 -rewrite fragment_to_full_substitution. now apply FullND.AllE.
 -now apply FullND.Exp.
 -apply FullND.Ctx. now apply List.in_map.
 -apply FullND.Pc.
Qed.
End ProofEmbedding.
Print Assumptions fragment_full_proof.
