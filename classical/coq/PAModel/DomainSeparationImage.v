(** Exact Separation quotation graph and atom lookup. The actual
    source-quotation interface is in QuotedSeparationInterface. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes NumericalEnvironments QuotationPayloads QuotationSchemaSkeleton.
Unset Implicit Arguments.

Definition domain_separation_graph M a theta left right q :=
  exists rhs forward backward iffcode allx exb,
    quotation_binary M SFAnd right theta rhs /\
    quotation_binary M SFImpl left rhs forward /\
    quotation_binary M SFImpl rhs left backward /\
    quotation_binary M SFAnd forward backward iffcode /\
    quotation_quantifier M true (succM M (succM M a)) (code_numeral M 1) iffcode allx /\
    quotation_quantifier M false (succM M a) (code_numeral M 1) allx exb /\
    quotation_quantifier M true a (code_numeral M 1) exb q.

Lemma separation_skeleton_atom_values M sources b c n k t equality i j x y v :
  environment_lookup M b c n (code_numeral M i) x ->
  environment_lookup M b c n (code_numeral M j) y ->
  skeleton_quotation M (SkeletonAtom equality i j) sources b c n k t v ->
  quotation_atom M equality x y t k v.
Proof.
  intros HX HY [u [w [HU [HW HV]]]].
  assert (u=x) by exact (environment_lookup_functional M b c n _ u x HU HX).
  assert (w=y) by exact (environment_lookup_functional M b c n _ w y HW HY).
  now subst u w.
Qed.

Print Assumptions separation_skeleton_atom_values.
