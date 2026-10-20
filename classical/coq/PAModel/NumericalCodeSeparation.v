(** Code separation for the exact K230 search, uniformly in every PA model.
    Parameters, formula codes and witnesses may all be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing
  CodeExpressions NumericalProofs CodeDescent CodeTags.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma search_zero_tag M :
  tagged_pair_graph M 0 (zeroM M) (zeroM M) (zeroM M).
Proof.
  exists (zeroM M). split; [apply pair_zero|].
  change (zeroM M = addM M (mulM M (code_numeral M 4) (zeroM M)) (zeroM M)).
  rewrite (Arithmetic.mul_comm M), Arithmetic.mul_zero, Arithmetic.add_zero.
  reflexivity.
Qed.

Lemma search_one_tag M :
  tagged_pair_graph M 1 (zeroM M) (zeroM M) (code_numeral M 1).
Proof.
  exists (zeroM M). split; [apply pair_zero|].
  rewrite (Arithmetic.mul_comm M), Arithmetic.mul_zero, Arithmetic.add_zero.
  reflexivity.
Qed.

Theorem search_implication_to_one_nonzero M a f :
  implication_graph M a (code_numeral M 1) f -> f <> zeroM M.
Proof.
  intros H E. subst f. apply implication_graph_tagged in H.
  destruct (tagged_pair_decode_unique M 0 0 a (code_numeral M 1)
    (zeroM M) (zeroM M) (zeroM M) ltac:(lia) ltac:(lia)
    H (search_zero_tag M)) as [_ [_ E]].
  apply (zero_ne_succ M (zeroM M)). symmetry. exact E.
Qed.

Lemma search_nonmember_tag_not_one M tag a b f :
  tag < 4 -> tag <> 1 -> tagged_pair_graph M tag a b f ->
  f <> code_numeral M 1.
Proof.
  intros Hbound Htag H E. subst f.
  exact (Htag (proj1 (tagged_pair_decode_unique M tag 1 a b
    (zeroM M) (zeroM M) (code_numeral M 1) Hbound ltac:(lia)
    H (search_one_tag M)))).
Qed.

Theorem search_implication_not_one M a b f :
  implication_graph M a b f -> f <> code_numeral M 1.
Proof.
  intro H. apply (search_nonmember_tag_not_one M 0 a b f);
    try lia. now apply implication_graph_tagged.
Qed.

Theorem search_universal_not_one M a b f :
  universal_graph M a b f -> f <> code_numeral M 1.
Proof.
  intro H. apply (search_nonmember_tag_not_one M 2 a b f);
    try lia. now apply universal_graph_tagged.
Qed.

Lemma search_code_implication_tag M rho A B f :
  code_relation M rho (E_wim A B) f ->
  exists a b, tagged_pair_graph M 0 a b f.
Proof.
  unfold E_wim. cbn [code_relation].
  intros [four [p [Hfour [[a [b [Ha [Hb Hp]]]] Hf]]]].
  subst four. exists a,b,p. split; [exact Hp|].
  rewrite coding_add_zero_r. exact Hf.
Qed.

Theorem search_code_implication_not_one M rho A B f :
  code_relation M rho (E_wim A B) f -> f <> code_numeral M 1.
Proof.
  intro H. destruct (search_code_implication_tag M rho A B f H) as [a [b Htag]].
  apply (search_nonmember_tag_not_one M 0 a b f); try lia. exact Htag.
Qed.

Lemma search_rho1_not_one M rho a b f :
  code_relation M rho (E_rho1 a b) f -> f <> code_numeral M 1.
Proof. unfold E_rho1,E_wex,E_wn. apply search_code_implication_not_one. Qed.
Lemma search_rho2_not_one M rho a b c f :
  code_relation M rho (E_rho2 a b c) f -> f <> code_numeral M 1.
Proof. unfold E_rho2. apply search_code_implication_not_one. Qed.
Lemma search_rho3_not_one M rho a b c f :
  code_relation M rho (E_rho3 a b c) f -> f <> code_numeral M 1.
Proof. unfold E_rho3. apply search_code_implication_not_one. Qed.
Lemma search_rho4_not_one M rho a b c f :
  code_relation M rho (E_rho4 a b c) f -> f <> code_numeral M 1.
Proof. unfold E_rho4. apply search_code_implication_not_one. Qed.
Lemma search_rho5_not_one M rho a b c f :
  code_relation M rho (E_rho5 a b c) f -> f <> code_numeral M 1.
Proof. unfold E_rho5. apply search_code_implication_not_one. Qed.
Lemma search_rho6_not_one M rho a b f :
  code_relation M rho (E_rho6 a b) f -> f <> code_numeral M 1.
Proof. unfold E_rho6. apply search_code_implication_not_one. Qed.
Lemma search_rho7_not_one M rho a b c f :
  code_relation M rho (E_rho7 a b c) f -> f <> code_numeral M 1.
Proof. unfold E_rho7. apply search_code_implication_not_one. Qed.
Lemma search_rho8_not_one M rho a b c u f :
  code_relation M rho (E_rho8 a b c u) f -> f <> code_numeral M 1.
Proof. unfold E_rho8. apply search_code_implication_not_one. Qed.
Lemma search_bundle_not_one M rho a b c f :
  code_relation M rho (E_bundle a b c) f -> f <> code_numeral M 1.
Proof. unfold E_bundle,E_wa,E_wn. apply search_code_implication_not_one. Qed.

Theorem search_axiom_rows_not_one M rho f :
  code_axiom_rows M rho f -> f <> code_numeral M 1.
Proof.
  unfold code_axiom_rows.
  intros [H|[H|[H|[H|[H|[H|[H|[H|[_ [_ H]]]]]]]]]];
    unfold code_row1,code_row2,code_row3,code_row4,code_row5,
      code_row6,code_row7,code_row8,code_bundle in H;
    eauto using search_rho1_not_one,search_rho2_not_one,search_rho3_not_one,
      search_rho4_not_one,search_rho5_not_one,search_rho6_not_one,
      search_rho7_not_one,search_rho8_not_one,search_bundle_not_one.
Qed.

Theorem search_axiom_not_one M f :
  K230_axiom_relation M f -> f <> code_numeral M 1.
Proof.
  intros [E|[a [b [c [u H]]]]].
  - subst f. apply zero_ne_succ.
  - exact (search_axiom_rows_not_one M _ f H).
Qed.

Print Assumptions search_implication_to_one_nonzero.
Print Assumptions search_universal_not_one.
Print Assumptions search_axiom_rows_not_one.
Print Assumptions search_axiom_not_one.
