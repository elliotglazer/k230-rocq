(** Exact existential witness interface for numerical quotient membership. *)
From PAModel Require Import Model CodeExpressions CodeDescent NumericalProofs NumericalVacuitySteps
  NamedExistential NamedBinderFresh NamedLeibnizSteps QuotientAtomTemplates QuotationPayloads QuotationFixedSource SetFormulaCodes FreshNames
  RawLawGraphs ContextualProofs NumericalEnvironments ContextualWitnessRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition raw_dmem_witness_expression T X Y K :=
  E_wa (E_wa (E_wel T K) (E_wel K Y)) (raw_atom_expression true T X K (CEadd K (CEconst 1))).

Lemma raw_dmem_unfold_expression T X Y K :
  raw_atom_expression false T X Y K = E_wex K (raw_dmem_witness_expression T X Y K).
Proof. reflexivity. Qed.

Definition raw_dmem_witness_graph M t x y k q dom mem eq child body :=
  membership_graph M t k dom /\ membership_graph M k y mem /\
  quotation_atom M true x k t (succM M k) eq /\
  quotation_binary M SFAnd dom mem child /\ quotation_binary M SFAnd child eq body /\
  named_exists_graph M k body q.

Theorem raw_dmem_witness_graph_total M t x y k q :
  quotation_atom M false x y t k q ->
  exists dom mem eq child body,raw_dmem_witness_graph M t x y k q dom mem eq child body.
Proof.
  intro HQ. set (rho:=t .: x .: y .: k .: fun _=>zeroM M).
  set (DE:=E_wel (CEvar 0) (CEvar 3)).
  set (ME:=E_wel (CEvar 3) (CEvar 2)).
  set (EE:=raw_atom_expression true (CEvar 0) (CEvar 1) (CEvar 3) (CEadd (CEvar 3) (CEconst 1))).
  destruct (code_relation_total M DE rho) as [dom HD].
  destruct (code_relation_total M ME rho) as [mem HM].
  destruct (code_relation_total M EE rho) as [eq HE].
  destruct (code_relation_total M (E_wa DE ME) rho) as [child HC].
  destruct (code_relation_total M (E_wa (E_wa DE ME) EE) rho) as [body HB].
  exists dom,mem,eq,child,body.
  assert (GD : membership_graph M t k dom).
  { exact (proj1 (ns_atom_expression M rho false (CEvar 0) (CEvar 3) t k dom eq_refl eq_refl) HD). }
  assert (GM : membership_graph M k y mem).
  { exact (proj1 (ns_atom_expression M rho false (CEvar 3) (CEvar 2) k y mem eq_refl eq_refl) HM). }
  assert (GE : quotation_atom M true x k t (succM M k) eq).
  { exact (proj1 (raw_atom_expression_graph M rho true (CEvar 0) (CEvar 1) (CEvar 3)
      (CEadd (CEvar 3) (CEconst 1)) t x k (succM M k) eq eq_refl eq_refl eq_refl
      (code_graph_fresh_successor M rho (CEvar 3) k eq_refl)) HE). }
  assert (GC : quotation_binary M SFAnd dom mem child).
  { exact (proj1 (quotation_binary_substitution_graph M rho SFAnd DE ME dom mem child HD HM) HC). }
  assert (GB : quotation_binary M SFAnd child eq body).
  { exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wa DE ME) EE child eq body HC HE) HB). }
  assert (GQ : code_relation M rho (E_wex (CEvar 3) (E_wa (E_wa DE ME) EE)) q).
  { change (code_relation M rho (E_wex (CEvar 3)
      (raw_dmem_witness_expression (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))) q).
    rewrite <-raw_dmem_unfold_expression.
    exact (proj2 (raw_atom_expression_graph M rho false (CEvar 0) (CEvar 1) (CEvar 2)
      (CEvar 3) t x y k q eq_refl eq_refl eq_refl eq_refl) HQ). }
  split;[exact GD|]. split;[exact GM|]. split;[exact GE|]. split;[exact GC|]. split;[exact GB|].
  exact (proj1 (named_exists_expression M rho (CEvar 3) (E_wa (E_wa DE ME) EE)
    k body q eq_refl HB) GQ).
Qed.

Theorem contextual_dmem_witness_bind M b c n t x y k q dom mem eq child body target d e m :
  raw_dmem_witness_graph M t x y k q dom mem eq child body ->
  context_fresh M b c n k -> formula_fresh M target k ->
  environment_cons M b c n body d e m ->
  contextually_provable M b c n q -> contextually_provable M d e m target ->
  contextually_provable M b c n target.
Proof.
  intros [_ [_ [_ [_ [_ HE]]]]] HF HT HC PQ PT.
  exact (contextual_witness_bind M b c n k body q target d e m HF HT HE HC PQ PT).
Qed.

Print Assumptions raw_dmem_unfold_expression.
Print Assumptions raw_dmem_witness_graph_total.
Print Assumptions contextual_dmem_witness_bind.
