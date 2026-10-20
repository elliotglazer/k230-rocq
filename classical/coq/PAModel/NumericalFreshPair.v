(** Actual pairing with a chosen container name and a fixed profile binder.
    Both the pair and the change of binder are numerical K proofs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs ProofTemplates NamedLeibnizSteps TemplateBinderFresh
  NumericalRawPair PairRebind TemplateNamedSubstitution.
Unset Implicit Arguments.

Lemma pair_ns_proof_reinstance M rho e s1 s2 values :
  (forall i,code_relation M rho (s1 i) (values i)) ->
  (forall i,code_relation M rho (s2 i) (values i)) ->
  ns_proof M rho (code_subst s1 e) -> ns_proof M rho (code_subst s2 e).
Proof.
  intros H1 H2 HP f HF. apply HP.
  apply (proj2 (code_subst_graph M rho s1 values H1 e f)).
  exact (proj1 (code_subst_graph M rho s2 values H2 e f) HF).
Qed.

Theorem numerical_fresh_pair M rho A B R Z Fresh av bv rv zv base :
  code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho R rv -> code_relation M rho Z zv -> code_relation M rho Fresh base ->
  av<>zv -> bv<>zv -> zv<>zeroM M -> rv=succM M (succM M base) ->
  coding_lt M (zeroM M) base -> coding_lt M av base ->
  coding_lt M bv base -> coding_lt M zv base ->
  ns_proof M rho (E_wex R (E_raw_pair A B R Z)).
Proof.
  intros HA HB HR HZ HF HAZ HBZ HZ0 ER H0 HAb HBb HZb.
  set (P:=CEadd (CEadd Fresh (CEconst 1)) (CEconst 1)).
  set (W:=CEadd P (CEconst 1)).
  assert (HP:code_relation M rho P rv).
  { rewrite ER. apply template_fresh_increment_graph,template_fresh_increment_graph,HF. }
  assert (HW:code_relation M rho W (succM M rv)).
  { apply template_fresh_increment_graph,HP. }
  assert (Hbr:coding_lt M base rv).
  { rewrite ER. eapply coding_lt_trans;apply coding_lt_succ. }
  assert (HAr:coding_lt M av rv) by exact (coding_lt_trans M av base rv HAb Hbr).
  assert (HBr:coding_lt M bv rv) by exact (coding_lt_trans M bv base rv HBb Hbr).
  assert (HZr:coding_lt M zv rv) by exact (coding_lt_trans M zv base rv HZb Hbr).
  assert (HPair:ns_proof M rho (E_wex P (E_raw_pair A B P Z))).
  { eapply ns_proof_mp.
    - exact (numerical_raw_pair_named M rho A B Fresh av bv base HA HB HF H0 HAb HBb).
    - apply (numerical_pair_exists_rebind M rho A B P W Z av bv rv (succM M rv) zv
        HA HB HP HW HZ).
      + exact (template_lt_different M (zeroM M) (succM M rv) (coding_zero_lt_succ M rv)).
      + exact HZ0.
      + exact (template_lt_different M zv (succM M rv)
          (coding_lt_trans M zv rv _ HZr (coding_lt_succ M rv))).
      + exact (not_eq_sym (template_lt_different M av (succM M rv)
          (coding_lt_trans M av rv _ HAr (coding_lt_succ M rv)))).
      + exact (not_eq_sym (template_lt_different M bv (succM M rv)
          (coding_lt_trans M bv rv _ HBr (coding_lt_succ M rv)))).
      + exact (not_eq_sym (template_lt_different M rv (succM M rv) (coding_lt_succ M rv))).
      + exact HAZ.
      + exact HBZ.
      + exact (template_lt_different M zv rv HZr). }
  set (body:=E_wex (CEvar 0) (E_raw_pair (CEvar 1) (CEvar 2) (CEvar 0) (CEvar 3))).
  set (s1:=fun i=>match i with 0=>P|1=>A|2=>B|3=>Z|_=>CEconst 0 end).
  set (s2:=fun i=>match i with 0=>R|1=>A|2=>B|3=>Z|_=>CEconst 0 end).
  set (values:=fun i=>match i with 0=>rv|1=>av|2=>bv|3=>zv|_=>zeroM M end).
  change (ns_proof M rho (code_subst s2 body)).
  apply (pair_ns_proof_reinstance M rho body s1 s2 values).
  - intros [|[|[|[|i]]]];assumption||reflexivity.
  - intros [|[|[|[|i]]]];assumption||reflexivity.
  - exact HPair.
Qed.

Print Assumptions pair_ns_proof_reinstance.
Print Assumptions numerical_fresh_pair.
