(** A Boolean checker for the eight-tag source syntax and its free-index
    bound. Certificates and all indices range over arbitrary PA models. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent
  NumericalEnvironments CodeTuples NumericalTraces.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition sb_atomic h := h=SFMember \/ h=SFEqual.
Definition sb_atom_heads M a b f :=
  sf_relation M SFMember a b f \/ sf_relation M SFEqual a b f.
Definition sb_unary_heads M a f :=
  sf_relation M SFAll a (zeroM M) f \/ sf_relation M SFEx a (zeroM M) f.
Definition sb_binary_heads M a b f :=
  sf_relation M SFAnd a b f \/ sf_relation M SFOr a b f \/ sf_relation M SFImpl a b f.

Definition sb_test M a b k v :=
  (coding_lt M a k /\ coding_lt M b k /\ v=code_numeral M 1) \/
  ((~coding_lt M a k \/ ~coding_lt M b k) /\ v=zeroM M).
Definition sb_test_formula (a b k v : term) : form :=
  (Peano.sless a k ∧ (Peano.sless b k ∧ v == num 1)) ∨
  (((Peano.sless a k → ⊥) ∨ (Peano.sless b k → ⊥)) ∧ v == zero).

Lemma sb_test_formula_correct M rho a b k v :
  holds M rho (sb_test_formula a b k v) <->
  sb_test M (evalM M rho a) (evalM M rho b) (evalM M rho k) (evalM M rho v).
Proof.
  unfold sb_test_formula,sb_test.
  match goal with |- _ <-> ?rhs =>
    change (((holds M rho (Peano.sless a k) /\ holds M rho (Peano.sless b k) /\
      evalM M rho v=code_numeral M 1) \/
      ((~holds M rho (Peano.sless a k) \/ ~holds M rho (Peano.sless b k)) /\
        evalM M rho v=zeroM M)) <-> rhs)
  end.
  rewrite !holds_sless. reflexivity.
Qed.

Definition sb_and M x y v :=
  (x=code_numeral M 1 /\ y=code_numeral M 1 /\ v=code_numeral M 1) \/
  ((x=zeroM M \/ y=zeroM M) /\ v=zeroM M).
Definition sb_and_formula (x y v : term) : form :=
  (x == num 1 ∧ (y == num 1 ∧ v == num 1)) ∨ ((x == zero ∨ y == zero) ∧ v == zero).
Lemma sb_and_formula_correct M rho x y v :
  holds M rho (sb_and_formula x y v) <->
  sb_and M (evalM M rho x) (evalM M rho y) (evalM M rho v).
Proof. reflexivity. Qed.

Definition sb_record M f k v r :=
  tuple7_graph M f k v (zeroM M) (zeroM M) (zeroM M) (zeroM M) r.
Definition sb_record_formula (f k v r : term) : form :=
  tuple7_formula f k v zero zero zero zero r.
Lemma sb_record_formula_correct M rho f k v r :
  holds M rho (sb_record_formula f k v r) <->
  sb_record M (evalM M rho f) (evalM M rho k) (evalM M rho v) (evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.
Lemma sb_record_total M f k v : exists r, sb_record M f k v r.
Proof. apply tuple7_total. Qed.
Lemma sb_record_injective M f k v f' k' v' r :
  sb_record M f k v r -> sb_record M f' k' v' r -> f=f' /\ k=k' /\ v=v'.
Proof.
  intros H H'. destruct (tuple7_injective M f k v _ _ _ _ f' k' v' _ _ _ _ r H H')
    as [Ef [Ek [Ev _]]]. auto.
Qed.

Definition sb_leaf M f k v :=
  (f=zeroM M /\ v=code_numeral M 1) \/ (sf_invalid M f /\ v=zeroM M) \/
  exists a b, sb_atom_heads M a b f /\ sb_test M a b k v.
Definition sb_leaf_formula (f k v : term) : form :=
  (f == zero ∧ v == num 1) ∨ ((sf_invalid_formula f ∧ v == zero) ∨
  ∃∃ ((sf_formula SFMember $1 $0 (code_lift2 f) ∨ sf_formula SFEqual $1 $0 (code_lift2 f)) ∧
    sb_test_formula $1 $0 (code_lift2 k) (code_lift2 v))).

Local Opaque holds sf_formula sf_invalid_formula sb_test_formula.
Lemma sb_leaf_formula_correct M rho f k v :
  holds M rho (sb_leaf_formula f k v) <->
  sb_leaf M (evalM M rho f) (evalM M rho k) (evalM M rho v).
Proof.
  unfold sb_leaf_formula,sb_leaf,sb_atom_heads.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_or.
  setoid_rewrite sf_invalid_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite sb_test_formula_correct. setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Definition sb_base M r := exists f k v, sb_record M f k v r /\ sb_leaf M f k v.
Definition sb_base_formula : form :=
  ∃∃∃ (sb_record_formula $2 $1 $0 $3 ∧ sb_leaf_formula $2 $1 $0).
Local Opaque sb_record_formula sb_leaf_formula.
Lemma sb_base_formula_correct M rho r : holds M (r .: rho) sb_base_formula <-> sb_base M r.
Proof.
  unfold sb_base_formula,sb_base. repeat setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite sb_record_formula_correct.
  setoid_rewrite sb_leaf_formula_correct. reflexivity.
Qed.

Definition sb_unary M r p := exists f k v a,
  sb_record M f k v r /\ sb_record M a (succM M k) v p /\ sb_unary_heads M a f.
Definition sb_unary_formula : form :=
  ∃∃∃∃ (sb_record_formula $3 $2 $1 $4 ∧ (sb_record_formula $0 (σ $2) $1 $5 ∧
    (sf_formula SFAll $0 zero $3 ∨ sf_formula SFEx $0 zero $3))).
Lemma sb_unary_formula_correct M rho r p :
  holds M (r .: p .: rho) sb_unary_formula <-> sb_unary M r p.
Proof.
  unfold sb_unary_formula,sb_unary,sb_unary_heads. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite holds_or.
  setoid_rewrite sb_record_formula_correct. setoid_rewrite sf_formula_correct. reflexivity.
Qed.

Definition sb_binary M r p q := exists f k v a b x y,
  sb_record M f k v r /\ sb_record M a k x p /\ sb_record M b k y q /\
  sb_binary_heads M a b f /\ sb_and M x y v.
Definition sb_binary_formula : form :=
  ∃∃∃∃∃∃∃ (sb_record_formula $6 $5 $4 $7 ∧ (sb_record_formula $3 $5 $1 $8 ∧
    (sb_record_formula $2 $5 $0 $9 ∧
    ((sf_formula SFAnd $3 $2 $6 ∨ (sf_formula SFOr $3 $2 $6 ∨ sf_formula SFImpl $3 $2 $6)) ∧
    sb_and_formula $1 $0 $4)))).
Local Opaque sb_and_formula.
Lemma sb_binary_formula_correct M rho r p q :
  holds M (r .: p .: q .: rho) sb_binary_formula <-> sb_binary M r p q.
Proof.
  unfold sb_binary_formula,sb_binary,sb_binary_heads. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_or.
  setoid_rewrite sb_record_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite sb_and_formula_correct. reflexivity.
Qed.

Lemma sb_base_bound : bounded 1 sb_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma sb_unary_bound : bounded 2 sb_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma sb_binary_bound : bounded 3 sb_binary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Definition sb_rules : NumericalRules :=
  {| rule_base_formula:=sb_base_formula; rule_base_bound:=sb_base_bound;
     rule_unary_formula:=sb_unary_formula; rule_unary_bound:=sb_unary_bound;
     rule_binary_formula:=sb_binary_formula; rule_binary_bound:=sb_binary_bound |}.
Lemma sb_rule_base M r : trace_base M sb_rules r <-> sb_base M r.
Proof. apply sb_base_formula_correct. Qed.
Lemma sb_rule_unary M r p : trace_unary M sb_rules r p <-> sb_unary M r p.
Proof. apply sb_unary_formula_correct. Qed.
Lemma sb_rule_binary M r p q : trace_binary M sb_rules r p q <-> sb_binary M r p q.
Proof. apply sb_binary_formula_correct. Qed.

Definition source_bounded_graph M f k v := exists r, sb_record M f k v r /\ trace_derives M sb_rules r.
Definition source_bounded_formula (f k v : term) : form :=
  ∃ (sb_record_formula f`[↑] k`[↑] v`[↑] $0 ∧ trace_derives_formula sb_rules $0).
Local Opaque trace_derives_formula.
Theorem source_bounded_formula_correct M rho f k v :
  holds M rho (source_bounded_formula f k v) <->
  source_bounded_graph M (evalM M rho f) (evalM M rho k) (evalM M rho v).
Proof.
  unfold source_bounded_formula,source_bounded_graph. setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite sb_record_formula_correct.
  setoid_rewrite trace_derives_formula_correct. unfold evalM. now setoid_rewrite eval_up.
Qed.
Theorem source_bounded_formula_bound : bounded 3 (source_bounded_formula $0 $1 $2).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Lemma sb_from_leaf M f k v : sb_leaf M f k v -> source_bounded_graph M f k v.
Proof.
  intro H. destruct (sb_record_total M f k v) as [r Hr]. exists r. split; [exact Hr|].
  apply trace_derives_base. apply sb_rule_base. exists f,k,v. auto.
Qed.
Lemma sb_from_unary M f k v a : sb_unary_heads M a f ->
  source_bounded_graph M a (succM M k) v -> source_bounded_graph M f k v.
Proof.
  intros Hf [p [Hp Hd]]. destruct (sb_record_total M f k v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_unary M sb_rules r p Hd).
  apply sb_rule_unary. exists f,k,v,a. auto.
Qed.
Lemma sb_from_binary M f k v a b x y : sb_binary_heads M a b f ->
  source_bounded_graph M a k x -> source_bounded_graph M b k y -> sb_and M x y v ->
  source_bounded_graph M f k v.
Proof.
  intros Hf [p [Hp Hd]] [q [Hq Hd']] Hv. destruct (sb_record_total M f k v) as [r Hr].
  exists r. split; [exact Hr|]. apply (trace_derives_binary M sb_rules r p q Hd Hd').
  apply sb_rule_binary. exists f,k,v,a,b,x,y. auto.
Qed.

Theorem source_bounded_cases M f k v : source_bounded_graph M f k v ->
  sb_leaf M f k v \/
  (exists a, sb_unary_heads M a f /\ source_bounded_graph M a (succM M k) v) \/
  (exists a b x y, sb_binary_heads M a b f /\ source_bounded_graph M a k x /\
    source_bounded_graph M b k y /\ sb_and M x y v).
Proof.
  intros [r [Hr Hd]]. destruct (trace_derives_inv M sb_rules r Hd)
    as [Hb|[[p [Hp Hu]]|[p [q [Hp [Hq Hbin]]]]]].
  - apply sb_rule_base in Hb. destruct Hb as [f' [k' [v' [Hr' H]]]].
    destruct (sb_record_injective M f k v f' k' v' r Hr Hr') as [Ef [Ek Ev]].
    subst f' k' v'. now left.
  - apply sb_rule_unary in Hu. destruct Hu as [f' [k' [v' [a [Hr' [Ha Hf]]]]]].
    destruct (sb_record_injective M f k v f' k' v' r Hr Hr') as [Ef [Ek Ev]].
    subst f' k' v'. right; left. exists a. split; [exact Hf|exists p; auto].
  - apply sb_rule_binary in Hbin.
    destruct Hbin as [f' [k' [v' [a [b [x [y [Hr' [Ha [Hb [Hf Hv]]]]]]]]]]].
    destruct (sb_record_injective M f k v f' k' v' r Hr Hr') as [Ef [Ek Ev]].
    subst f' k' v'. right; right. exists a,b,x,y. split; [exact Hf|].
    split; [exists p; auto|]. split; [exists q; auto|exact Hv].
Qed.

Lemma sb_zero_one M : zeroM M <> code_numeral M 1.
Proof.
  intro H. exact (@Peano.zero_succ (carrier M) (raw_interpretation M)
    (fun ax Ha rho => axioms M ax rho Ha) (zeroM M) H).
Qed.
Definition sb_boolean M v := v=zeroM M \/ v=code_numeral M 1.
Lemma sb_test_boolean M a b k v : sb_test M a b k v -> sb_boolean M v.
Proof. intros [[_ [_ H]]|[_ H]]; [now right|now left]. Qed.
Lemma sb_test_total M a b k : exists v, sb_test M a b k v.
Proof.
  destruct (environment_lt_cases M a k) as [Ha|Ha], (environment_lt_cases M b k) as [Hb|Hb].
  - exists (code_numeral M 1). left. auto.
  - exists (zeroM M). right. auto.
  - exists (zeroM M). right. auto.
  - exists (zeroM M). right. auto.
Qed.
Lemma sb_test_functional M a b k v w : sb_test M a b k v -> sb_test M a b k w -> v=w.
Proof. unfold sb_test. intuition congruence. Qed.
Lemma sb_and_boolean M x y v : sb_and M x y v -> sb_boolean M v.
Proof. intros [[_ [_ H]]|[_ H]]; [now right|now left]. Qed.
Lemma sb_and_total M x y : sb_boolean M x -> sb_boolean M y -> exists v, sb_and M x y v.
Proof.
  intros [Hx|Hx] [Hy|Hy]; subst x y.
  - exists (zeroM M). right. auto.
  - exists (zeroM M). right. auto.
  - exists (zeroM M). right. auto.
  - exists (code_numeral M 1). left. auto.
Qed.
Lemma sb_and_functional M x y v w : sb_and M x y v -> sb_and M x y w -> v=w.
Proof. pose proof (sb_zero_one M). unfold sb_and. intuition congruence. Qed.

Lemma sb_atom_heads_spec M a b f :
  sb_atom_heads M a b f <-> exists h, sb_atomic h /\ sf_relation M h a b f.
Proof.
  split; [intros [H|H]; [exists SFMember|exists SFEqual]; unfold sb_atomic; auto|].
  intros [h [[Hh|Hh] H]]; subst h; [now left|now right].
Qed.
Lemma sb_unary_heads_spec M a f :
  sb_unary_heads M a f <-> exists h, sf_unary h /\ sf_relation M h a (zeroM M) f.
Proof.
  split; [intros [H|H]; [exists SFAll|exists SFEx]; unfold sf_unary; auto|].
  intros [h [[Hh|Hh] H]]; subst h; [now left|now right].
Qed.
Lemma sb_binary_heads_spec M a b f :
  sb_binary_heads M a b f <-> exists h, sf_binary h /\ sf_relation M h a b f.
Proof.
  split; [intros [H|[H|H]]; [exists SFAnd|exists SFOr|exists SFImpl]; unfold sf_binary; auto|].
  intros [h [[Hh|[Hh|Hh]] H]]; subst h; [now left|right;now left|right;now right].
Qed.
Lemma sb_atomic_second M h b : sb_atomic h -> sf_payload_second M h b=b.
Proof. intros [H|H]; subst h; reflexivity. Qed.
Lemma sb_binary_second M h b : sf_binary h -> sf_payload_second M h b=b.
Proof. intros [H|[H|H]]; subst h; reflexivity. Qed.

Lemma sb_bad_constructor M f h a b : (f=zeroM M \/ sf_invalid M f) -> sf_relation M h a b f -> False.
Proof.
  intros [E|Hb] Hf.
  - exact (sf_relation_nonzero M h a b f Hf E).
  - exact (sf_invalid_not_constructor M h a b f Hb Hf).
Qed.
Lemma sb_zero_inv M k v : source_bounded_graph M (zeroM M) k v -> v=code_numeral M 1.
Proof.
  intro H. apply source_bounded_cases in H.
  destruct H as [[[Ef Ev]|[[Hb Ev]|[a [b [Ha Ht]]]]]|[[a [Hu Hc]]|[a [b [x [y [Hb Hc]]]]]]].
  - exact Ev.
  - exfalso. exact (sf_invalid_not_zero M _ Hb eq_refl).
  - apply sb_atom_heads_spec in Ha. destruct Ha as [h [_ Hf]].
    exfalso. eapply sb_bad_constructor; [left; reflexivity|exact Hf].
  - apply sb_unary_heads_spec in Hu. destruct Hu as [h [_ Hf]].
    exfalso. eapply sb_bad_constructor; [left; reflexivity|exact Hf].
  - apply sb_binary_heads_spec in Hb. destruct Hb as [h [_ Hf]].
    exfalso. eapply sb_bad_constructor; [left; reflexivity|exact Hf].
Qed.
Lemma sb_invalid_inv M f k v : sf_invalid M f -> source_bounded_graph M f k v -> v=zeroM M.
Proof.
  intros Hbad H. apply source_bounded_cases in H.
  destruct H as [[[Ef Ev]|[[Hb Ev]|[a [b [Ha Ht]]]]]|[[a [Hu Hc]]|[a [b [x [y [Hb Hc]]]]]]].
  - exfalso. exact (sf_invalid_not_zero M f Hbad Ef).
  - exact Ev.
  - apply sb_atom_heads_spec in Ha. destruct Ha as [h [_ Hf]].
    exfalso. eapply sb_bad_constructor; [right;exact Hbad|exact Hf].
  - apply sb_unary_heads_spec in Hu. destruct Hu as [h [_ Hf]].
    exfalso. eapply sb_bad_constructor; [right;exact Hbad|exact Hf].
  - apply sb_binary_heads_spec in Hb. destruct Hb as [h [_ Hf]].
    exfalso. eapply sb_bad_constructor; [right;exact Hbad|exact Hf].
Qed.

Lemma sb_atom_inv M h a b f k v : sb_atomic h -> sf_relation M h a b f ->
  source_bounded_graph M f k v -> sb_test M a b k v.
Proof.
  intros Hh Hf H. apply source_bounded_cases in H.
  destruct H as [[[Ef Ev]|[[Hb Ev]|[a' [b' [Ha Ht]]]]]|[[a' [Hu Hc]]|[a' [b' [x [y [Hb Hc]]]]]]].
  - exfalso. eapply sb_bad_constructor; [left;exact Ef|exact Hf].
  - exfalso. eapply sb_bad_constructor; [right;exact Hb|exact Hf].
  - apply sb_atom_heads_spec in Ha. destruct Ha as [h' [Hh' Hf']].
    destruct (sf_relation_injective M h h' a b a' b' f Hf Hf') as [Eh [Ea Eb]].
    subst h' a'. rewrite !sb_atomic_second in Eb by exact Hh. now subst b'.
  - apply sb_unary_heads_spec in Hu. destruct Hu as [h' [Hh' Hf']].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    subst h'. unfold sb_atomic in Hh. unfold sf_unary in Hh'. intuition congruence.
  - apply sb_binary_heads_spec in Hb. destruct Hb as [h' [Hh' Hf']].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    subst h'. unfold sb_atomic in Hh. unfold sf_binary in Hh'. intuition congruence.
Qed.

Lemma sb_unary_inv M h a f k v : sf_unary h -> sf_relation M h a (zeroM M) f ->
  source_bounded_graph M f k v -> source_bounded_graph M a (succM M k) v.
Proof.
  intros Hh Hf H. apply source_bounded_cases in H.
  destruct H as [[[Ef Ev]|[[Hb Ev]|[a' [b' [Ha Ht]]]]]|[[a' [Hu Hc]]|[a' [b' [x [y [Hb Hc]]]]]]].
  - exfalso. eapply sb_bad_constructor; [left;exact Ef|exact Hf].
  - exfalso. eapply sb_bad_constructor; [right;exact Hb|exact Hf].
  - apply sb_atom_heads_spec in Ha. destruct Ha as [h' [Hh' Hf']].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    subst h'. unfold sf_unary in Hh. unfold sb_atomic in Hh'. intuition congruence.
  - apply sb_unary_heads_spec in Hu. destruct Hu as [h' [Hh' Hf']].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [_ [Ea _]]. now subst a'.
  - apply sb_binary_heads_spec in Hb. destruct Hb as [h' [Hh' Hf']].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    subst h'. unfold sf_unary in Hh. unfold sf_binary in Hh'. intuition congruence.
Qed.

Lemma sb_binary_inv M h a b f k v : sf_binary h -> sf_relation M h a b f ->
  source_bounded_graph M f k v ->
  exists x y, source_bounded_graph M a k x /\ source_bounded_graph M b k y /\ sb_and M x y v.
Proof.
  intros Hh Hf H. apply source_bounded_cases in H.
  destruct H as [[[Ef Ev]|[[Hb Ev]|[a' [b' [Ha Ht]]]]]|[[a' [Hu Hc]]|[a' [b' [x [y [Hb Hc]]]]]]].
  - exfalso. eapply sb_bad_constructor; [left;exact Ef|exact Hf].
  - exfalso. eapply sb_bad_constructor; [right;exact Hb|exact Hf].
  - apply sb_atom_heads_spec in Ha. destruct Ha as [h' [Hh' Hf']].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    subst h'. unfold sf_binary in Hh. unfold sb_atomic in Hh'. intuition congruence.
  - apply sb_unary_heads_spec in Hu. destruct Hu as [h' [Hh' Hf']].
    destruct (sf_relation_injective M _ _ _ _ _ _ _ Hf Hf') as [Eh _].
    subst h'. unfold sf_binary in Hh. unfold sf_unary in Hh'. intuition congruence.
  - apply sb_binary_heads_spec in Hb. destruct Hb as [h' [Hh' Hf']].
    destruct (sf_relation_injective M h h' a b a' b' f Hf Hf') as [Eh [Ea Eb]].
    subst h' a'. rewrite !sb_binary_second in Eb by exact Hh. subst b'. exists x,y. exact Hc.
Qed.

Definition sb_total_boolean_at M f :=
  forall k, exists v, source_bounded_graph M f k v /\ sb_boolean M v.
Definition sb_total_boolean_formula : form :=
  ∀∃ (source_bounded_formula $2 $1 $0 ∧ ($0 == zero ∨ $0 == num 1)).
Local Opaque source_bounded_formula.
Lemma sb_total_boolean_definable M : Definable1 M (sb_total_boolean_at M).
Proof.
  exists sb_total_boolean_formula,(fun _ => zeroM M).
  intro f. unfold sb_total_boolean_formula,sb_total_boolean_at,sb_boolean.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite holds_or.
  setoid_rewrite source_bounded_formula_correct. reflexivity.
Qed.

Theorem source_bounded_total_boolean M f : sb_total_boolean_at M f.
Proof.
  revert f. apply (sf_code_induction M (sb_total_boolean_at M)).
  - apply sb_total_boolean_definable.
  - intro k. exists (code_numeral M 1). split; [apply sb_from_leaf; left; auto|now right].
  - intros f Hbad k. exists (zeroM M). split; [apply sb_from_leaf; right;left;auto|now left].
  - intros a b f Hf k. destruct (sb_test_total M a b k) as [v Hv]. exists v. split.
    + apply sb_from_leaf. right;right. exists a,b. split; [now left|exact Hv].
    + exact (sb_test_boolean M a b k v Hv).
  - intros a b f Hf k. destruct (sb_test_total M a b k) as [v Hv]. exists v. split.
    + apply sb_from_leaf. right;right. exists a,b. split; [now right|exact Hv].
    + exact (sb_test_boolean M a b k v Hv).
  - intros h a b f Hh Hf IHa IHb k.
    destruct (IHa k) as [x [Hx Hxb]], (IHb k) as [y [Hy Hyb]].
    destruct (sb_and_total M x y Hxb Hyb) as [v Hv]. exists v. split.
    + apply (sb_from_binary M f k v a b x y); try assumption.
      apply sb_binary_heads_spec. exists h. auto.
    + exact (sb_and_boolean M x y v Hv).
  - intros h a f Hh Hf IH k. destruct (IH (succM M k)) as [v [Hv Hvb]].
    exists v. split; [|exact Hvb]. apply (sb_from_unary M f k v a); [|exact Hv].
    apply sb_unary_heads_spec. exists h. auto.
Qed.
Corollary source_bounded_total M f k : exists v, source_bounded_graph M f k v.
Proof. destruct (source_bounded_total_boolean M f k) as [v [Hv _]]. now exists v. Qed.

Definition sb_functional_at M f := forall k v w,
  source_bounded_graph M f k v -> source_bounded_graph M f k w -> v=w.
Definition sb_functional_formula : form :=
  ∀∀∀ (source_bounded_formula $3 $2 $1 → source_bounded_formula $3 $2 $0 → $1 == $0).
Lemma sb_functional_definable M : Definable1 M (sb_functional_at M).
Proof.
  exists sb_functional_formula,(fun _ => zeroM M). intro f.
  unfold sb_functional_formula,sb_functional_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_formula_correct. reflexivity.
Qed.
Theorem source_bounded_functional M f : sb_functional_at M f.
Proof.
  revert f. apply (sf_code_induction M (sb_functional_at M)).
  - apply sb_functional_definable.
  - intros k v w Hv Hw. rewrite (sb_zero_inv M k v Hv), (sb_zero_inv M k w Hw). reflexivity.
  - intros f Hbad k v w Hv Hw.
    rewrite (sb_invalid_inv M f k v Hbad Hv), (sb_invalid_inv M f k w Hbad Hw). reflexivity.
  - intros a b f Hf k v w Hv Hw. apply (sb_test_functional M a b k v w).
    + exact (sb_atom_inv M SFMember a b f k v (or_introl eq_refl) Hf Hv).
    + exact (sb_atom_inv M SFMember a b f k w (or_introl eq_refl) Hf Hw).
  - intros a b f Hf k v w Hv Hw. apply (sb_test_functional M a b k v w).
    + exact (sb_atom_inv M SFEqual a b f k v (or_intror eq_refl) Hf Hv).
    + exact (sb_atom_inv M SFEqual a b f k w (or_intror eq_refl) Hf Hw).
  - intros h a b f Hh Hf IHa IHb k v w Hv Hw.
    destruct (sb_binary_inv M h a b f k v Hh Hf Hv) as [x [y [Hx [Hy Hout]]]].
    destruct (sb_binary_inv M h a b f k w Hh Hf Hw) as [x' [y' [Hx' [Hy' Hout']]]].
    assert (Ex : x=x') by exact (IHa k x x' Hx Hx').
    assert (Ey : y=y') by exact (IHb k y y' Hy Hy').
    subst x' y'. exact (sb_and_functional M x y v w Hout Hout').
  - intros h a f Hh Hf IH k v w Hv Hw. apply (IH (succM M k) v w).
    + exact (sb_unary_inv M h a f k v Hh Hf Hv).
    + exact (sb_unary_inv M h a f k w Hh Hf Hw).
Qed.
Theorem source_bounded_boolean M f k v : source_bounded_graph M f k v -> sb_boolean M v.
Proof.
  intro Hv. destruct (source_bounded_total_boolean M f k) as [w [Hw Hwb]].
  assert (E : v=w) by exact (source_bounded_functional M f k v w Hv Hw).
  now subst v.
Qed.

(** Exact recursive equations, including rejection of malformed top-level
    constructors. The unary equation increases the free-index allowance. *)
Theorem source_bounded_falsity M k v :
  source_bounded_graph M (zeroM M) k v <-> v=code_numeral M 1.
Proof. split; [apply sb_zero_inv|intro E;subst v;apply sb_from_leaf;left;auto]. Qed.
Theorem source_bounded_invalid M f k v : sf_invalid M f ->
  (source_bounded_graph M f k v <-> v=zeroM M).
Proof.
  intro H. split; [apply sb_invalid_inv;exact H|].
  intro E;subst v;apply sb_from_leaf;right;left;auto.
Qed.
Theorem source_bounded_atom M h a b f k v : sb_atomic h -> sf_relation M h a b f ->
  (source_bounded_graph M f k v <-> sb_test M a b k v).
Proof.
  intros Hh Hf. split; [apply (sb_atom_inv M h a b f k v Hh Hf)|].
  intro Hv. apply sb_from_leaf. right;right. exists a,b. split; [|exact Hv].
  apply sb_atom_heads_spec. exists h. auto.
Qed.
Theorem source_bounded_binary M h a b f k v : sf_binary h -> sf_relation M h a b f ->
  (source_bounded_graph M f k v <-> exists x y,
    source_bounded_graph M a k x /\ source_bounded_graph M b k y /\ sb_and M x y v).
Proof.
  intros Hh Hf. split; [apply (sb_binary_inv M h a b f k v Hh Hf)|].
  intros [x [y [Hx [Hy Hv]]]]. apply (sb_from_binary M f k v a b x y); try assumption.
  apply sb_binary_heads_spec. exists h. auto.
Qed.
Theorem source_bounded_unary M h a f k v : sf_unary h -> sf_relation M h a (zeroM M) f ->
  (source_bounded_graph M f k v <-> source_bounded_graph M a (succM M k) v).
Proof.
  intros Hh Hf. split; [apply (sb_unary_inv M h a f k v Hh Hf)|].
  intro Hv. apply (sb_from_unary M f k v a); [|exact Hv].
  apply sb_unary_heads_spec. exists h. auto.
Qed.

Definition source_bounded M f k := source_bounded_graph M f k (code_numeral M 1).
Definition source_bounded_accept_formula (f k : term) := source_bounded_formula f k (num 1).
Theorem source_bounded_accept_formula_correct M rho f k :
  holds M rho (source_bounded_accept_formula f k) <->
  source_bounded M (evalM M rho f) (evalM M rho k).
Proof. apply source_bounded_formula_correct. Qed.
Theorem source_bounded_definable M k : Definable1 M (fun f => source_bounded M f k).
Proof.
  exists (source_bounded_accept_formula $0 $1),(k .: fun _ => zeroM M).
  intro f. symmetry. apply source_bounded_accept_formula_correct.
Qed.
Theorem source_bounded_reject_iff M f k :
  source_bounded_graph M f k (zeroM M) <-> ~source_bounded M f k.
Proof.
  split.
  - intros H0 H1. apply (sb_zero_one M). exact (source_bounded_functional M f k _ _ H0 H1).
  - intro Hnot. destruct (source_bounded_total_boolean M f k) as [v [Hv [E|E]]]; subst v.
    + exact Hv.
    + contradiction.
Qed.
Theorem source_bounded_decides M f k : source_bounded M f k \/ ~source_bounded M f k.
Proof.
  destruct (source_bounded_total_boolean M f k) as [v [Hv [E|E]]]; subst v.
  - right. now apply source_bounded_reject_iff.
  - now left.
Qed.

Theorem source_bounded_accept_falsity M k : source_bounded M (zeroM M) k.
Proof. apply source_bounded_falsity. reflexivity. Qed.
Theorem source_bounded_reject_invalid M f k : sf_invalid M f -> ~source_bounded M f k.
Proof.
  intro H. apply source_bounded_reject_iff. apply source_bounded_invalid; auto.
Qed.
Theorem source_bounded_accept_atom M h a b f k : sb_atomic h -> sf_relation M h a b f ->
  (source_bounded M f k <-> coding_lt M a k /\ coding_lt M b k).
Proof.
  intros Hh Hf. unfold source_bounded. rewrite (source_bounded_atom M h a b f k _ Hh Hf).
  unfold sb_test. pose proof (sb_zero_one M). intuition congruence.
Qed.
Theorem source_bounded_accept_binary M h a b f k : sf_binary h -> sf_relation M h a b f ->
  (source_bounded M f k <-> source_bounded M a k /\ source_bounded M b k).
Proof.
  intros Hh Hf. unfold source_bounded. rewrite (source_bounded_binary M h a b f k _ Hh Hf).
  split.
  - intros [x [y [Hx [Hy Hout]]]]. destruct Hout as [[Ex [Ey Ev]]|[_ Ev]].
    + subst x y. auto.
    + exfalso. apply (sb_zero_one M). symmetry. exact Ev.
  - intros [Hx Hy]. exists (code_numeral M 1),(code_numeral M 1).
    split; [exact Hx|]. split; [exact Hy|]. left. auto.
Qed.
Theorem source_bounded_accept_unary M h a f k : sf_unary h -> sf_relation M h a (zeroM M) f ->
  (source_bounded M f k <-> source_bounded M a (succM M k)).
Proof. apply source_bounded_unary. Qed.
