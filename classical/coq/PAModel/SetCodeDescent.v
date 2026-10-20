(** Internal decoding and structural induction for SetFormulaCodes' eight
    tags. Invalid TOP-LEVEL codes are explicit. Constructor-shaped codes can
    still have invalid descendants; no well-formedness premise is hidden. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula Pairing CodeExpressions NumericalProofs CourseOfValues
  CodeDescent SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.

Definition sf_tagged_graph M tag (a b f : carrier M) : Prop :=
  exists p, pair_graph M a b p /\
    f = addM M (mulM M (code_numeral M 8) p) (code_numeral M tag).

Definition sf_tagged_formula (tag : nat) (a b f : pa_term) : pa_form :=
  ∃ (pair_formula a`[↑] b`[↑] $0 ∧
    f`[↑] == (num 8 ⊗ $0) ⊕ num tag).

Lemma sf_tagged_formula_correct M rho tag a b f :
  holds M rho (sf_tagged_formula tag a b f) <->
  sf_tagged_graph M tag (evalM M rho a) (evalM M rho b) (evalM M rho f).
Proof.
  unfold sf_tagged_formula,sf_tagged_graph. rewrite holds_exists.
  setoid_rewrite holds_and. setoid_rewrite pair_formula_correct.
  unfold holds,evalM. cbn. setoid_rewrite eval_up.
  change ((exists p, pair_graph M (evalM M rho a) (evalM M rho b) p /\
    evalM M rho f = addM M (mulM M (evalM M (p .: rho) (num 8)) p)
      (evalM M (p .: rho) (num tag))) <->
    (exists p, pair_graph M (evalM M rho a) (evalM M rho b) p /\
      evalM M rho f = addM M (mulM M (code_numeral M 8) p) (code_numeral M tag))).
  setoid_rewrite code_eval_num. reflexivity.
Qed.

Definition sf_payload_second M (h : sf_head) (b : carrier M) : carrier M :=
  match h with SFAll | SFEx => zeroM M | _ => b end.

Lemma sf_expression_pair_graph M env tag A B a b f :
  code_relation M env A a -> code_relation M env B b ->
  (code_relation M env (E_sf_pair tag A B) f <-> sf_tagged_graph M tag a b f).
Proof.
  intros HA HB. unfold E_sf_pair. cbn [code_relation]. split.
  - intros [q [r [Hq [Hr Hf]]]].
    destruct Hq as [eight [p [H8 [Hp Hq]]]].
    destruct Hp as [x [y [Hx [Hy Hp]]]].
    assert (Ex : x=a) by exact (code_relation_functional M A env x a Hx HA).
    assert (Ey : y=b) by exact (code_relation_functional M B env y b Hy HB).
    subst x y eight r q. now exists p.
  - intros [p [Hp Hf]].
    exists (mulM M (code_numeral M 8) p),(code_numeral M tag).
    split; [|auto]. exists (code_numeral M 8),p.
    split; [reflexivity|]. split; [|reflexivity].
    exists a,b. auto.
Qed.

Theorem sf_relation_graph M h a b f :
  sf_relation M h a b f <->
  sf_tagged_graph M (sf_tag h) a (sf_payload_second M h b) f.
Proof.
  destruct h; unfold sf_relation,E_sf; cbn [sf_payload_second sf_tag];
    apply sf_expression_pair_graph; reflexivity.
Qed.

Lemma sf_tag_positive h : sf_tag h <> 0.
Proof. destruct h; cbn; lia. Qed.
Lemma sf_tag_bound h : sf_tag h < 8.
Proof. destruct h; cbn; lia. Qed.
Lemma sf_tag_injective h h' : sf_tag h=sf_tag h' -> h=h'.
Proof. destruct h,h'; cbn; congruence. Qed.

Lemma sf_numeral_lt M n m : n<m ->
  coding_lt M (code_numeral M n) (code_numeral M m).
Proof.
  induction m in n |- *; intro H; [lia|].
  destruct n; [apply coding_zero_lt_succ|].
  apply coding_lt_succ_cancel. apply IHm. lia.
Qed.

Section Decoder.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation N := (code_numeral M).
Add Ring sf_decoder_ring : (model_semiring M).

Lemma sf_tagged_total tag a b : exists f, sf_tagged_graph M tag a b f.
Proof.
  destruct (pair_total M a b) as [p Hp]. exists (N 8*p+N tag),p. auto.
Qed.

Lemma sf_tagged_functional tag a b f g :
  sf_tagged_graph M tag a b f -> sf_tagged_graph M tag a b g -> f=g.
Proof.
  intros [p [Hp ->]] [q [Hq ->]].
  now rewrite (pair_functional M a b p q Hp Hq).
Qed.

Theorem sf_tagged_decode_unique tag tag' a b a' b' f :
  tag<8 -> tag'<8 ->
  sf_tagged_graph M tag a b f -> sf_tagged_graph M tag' a' b' f ->
  tag=tag' /\ a=a' /\ b=b'.
Proof.
  intros Ht Ht' [p [Hp Hf]] [q [Hq Hf']].
  assert (He : N tag+p*N 8=N tag'+q*N 8).
  { rewrite (Arithmetic.add_comm M), (Arithmetic.add_comm M (N tag')),
      (mul_comm M p), (mul_comm M q). congruence. }
  destruct (@Peano.iFac_unique D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) (N 8) p (N tag) q (N tag')
    (sf_numeral_lt M tag 8 Ht) (sf_numeral_lt M tag' 8 Ht') He) as [Ep Et].
  assert (Etag : tag=tag').
  { apply (@Peano.inu_inj D (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H)). now rewrite !numeral_inu. }
  subst q. split; [exact Etag|]. exact (pair_injective M p a b a' b' Hp Hq).
Qed.

Theorem sf_tagged_decomposition f :
  exists tag, tag<8 /\ exists a b, sf_tagged_graph M tag a b f.
Proof.
  destruct (@Peano.iEuclid' D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) f 8 ltac:(lia)) as [q [r [Hr Hf]]].
  rewrite !numeral_inu in Hf.
  destruct (pair_surjective M q) as [a [b Hp]].
  exists r. split; [exact Hr|]. exists a,b,q. split; [exact Hp|].
  rewrite Hf. change (q*N 8+N r=N 8*q+N r). ring.
Qed.

Lemma sf_tagged_zero : sf_tagged_graph M 0 O O O.
Proof. exists O. split; [apply pair_zero|]. cbn [code_numeral]. ring. Qed.

Theorem sf_tagged_at_zero tag a b : tag<8 ->
  sf_tagged_graph M tag a b O -> tag=0 /\ a=O /\ b=O.
Proof.
  intros Htag H. exact (sf_tagged_decode_unique tag 0 a b O O O Htag ltac:(lia) H sf_tagged_zero).
Qed.

Theorem sf_tagged_positive_descent tag a b f : tag<>0 ->
  sf_tagged_graph M tag a b f -> coding_lt M a f /\ coding_lt M b f.
Proof.
  intros Htag [p [Hp Ef]]. destruct tag as [|tag]; [contradiction|].
  destruct (pair_coordinate_bounds M a b p Hp) as [[d Ed] [e Ee]].
  change (f=S (N 7)*p+S (N tag)) in Ef.
  rewrite (mul_succ M (N 7) p) in Ef.
  split.
  - exists (d+N 7*p+N tag). rewrite Ef.
    rewrite (succ_as_add M (N tag)), (succ_as_add M (a+(d+N 7*p+N tag))).
    rewrite Ed at 1. ring.
  - exists (e+N 7*p+N tag). rewrite Ef.
    rewrite (succ_as_add M (N tag)), (succ_as_add M (b+(e+N 7*p+N tag))).
    rewrite Ee at 1. ring.
Qed.

Theorem sf_relation_descent h a b f : sf_relation M h a b f ->
  coding_lt M a f /\ coding_lt M (sf_payload_second M h b) f.
Proof.
  intro H. apply (sf_tagged_positive_descent (sf_tag h) a (sf_payload_second M h b) f).
  - apply sf_tag_positive.
  - now apply sf_relation_graph.
Qed.

Theorem sf_relation_nonzero h a b f : sf_relation M h a b f -> f<>O.
Proof.
  intro H. destruct (sf_relation_descent h a b f H) as [Ha _].
  intro E. subst f. exact (coding_not_lt_zero M a Ha).
Qed.

Theorem sf_relation_injective h h' a b a' b' f :
  sf_relation M h a b f -> sf_relation M h' a' b' f ->
  h=h' /\ a=a' /\ sf_payload_second M h b=sf_payload_second M h' b'.
Proof.
  intros H H'. apply sf_relation_graph in H,H'.
  destruct (sf_tagged_decode_unique (sf_tag h) (sf_tag h') a
    (sf_payload_second M h b) a' (sf_payload_second M h' b') f
    (sf_tag_bound h) (sf_tag_bound h') H H') as [E [Ea Eb]].
  split; [now apply sf_tag_injective|auto].
Qed.

End Decoder.

(** A single decoder relation whose tag is itself a model element.  The
    finite host-level tag case distinction above proves its totality. *)
Definition sf_decode_graph M (tag a b f : carrier M) : Prop :=
  coding_lt M tag (code_numeral M 8) /\ exists p, pair_graph M a b p /\
    f = addM M (mulM M (code_numeral M 8) p) tag.

Definition sf_decode_formula (tag a b f : pa_term) : pa_form :=
  Peano.sless tag (num 8) ∧
  ∃ (pair_formula a`[↑] b`[↑] $0 ∧ f`[↑] == (num 8 ⊗ $0) ⊕ tag`[↑]).

Lemma sf_eval_lift1 M rho x (t : pa_term) :
  evalM M (x .: rho) t`[↑] = evalM M rho t.
Proof. unfold evalM. now rewrite eval_up. Qed.

Lemma sf_holds_equal M rho (a b : pa_term) :
  holds M rho (a == b) <-> evalM M rho a = evalM M rho b.
Proof. reflexivity. Qed.

Theorem sf_decode_formula_correct M rho tag a b f :
  holds M rho (sf_decode_formula tag a b f) <->
  sf_decode_graph M (evalM M rho tag) (evalM M rho a) (evalM M rho b) (evalM M rho f).
Proof.
  unfold sf_decode_formula,sf_decode_graph.
  rewrite holds_and,less_formula_correct. setoid_rewrite holds_exists.
  setoid_rewrite holds_and. setoid_rewrite pair_formula_correct.
  setoid_rewrite sf_holds_equal.
  change ((coding_lt M (evalM M rho tag) (code_numeral M 8) /\
    exists p, pair_graph M (evalM M (p .: rho) a`[↑]) (evalM M (p .: rho) b`[↑]) p /\
      evalM M (p .: rho) f`[↑] = addM M (mulM M (code_numeral M 8) p)
        (evalM M (p .: rho) tag`[↑])) <->
    (coding_lt M (evalM M rho tag) (code_numeral M 8) /\
    exists p, pair_graph M (evalM M rho a) (evalM M rho b) p /\
      evalM M rho f = addM M (mulM M (code_numeral M 8) p) (evalM M rho tag))).
  setoid_rewrite sf_eval_lift1. reflexivity.
Qed.

Theorem sf_decode_total M f : exists tag a b, sf_decode_graph M tag a b f.
Proof.
  destruct (sf_tagged_decomposition M f) as [tag [Ht [a [b H]]]].
  exists (code_numeral M tag),a,b. split; [now apply sf_numeral_lt|exact H].
Qed.

Theorem sf_decode_unique M tag a b tag' a' b' f :
  sf_decode_graph M tag a b f -> sf_decode_graph M tag' a' b' f ->
  tag=tag' /\ a=a' /\ b=b'.
Proof.
  intros [Ht [p [Hp Hf]]] [Ht' [q [Hq Hf']]].
  assert (He : addM M tag (mulM M p (code_numeral M 8)) =
      addM M tag' (mulM M q (code_numeral M 8))).
  { rewrite (Arithmetic.add_comm M), (Arithmetic.add_comm M tag'),
      (mul_comm M p), (mul_comm M q). congruence. }
  destruct (@Peano.iFac_unique (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) (code_numeral M 8)
    p tag q tag' Ht Ht' He) as [Ep Et].
  subst q. split; [exact Et|]. exact (pair_injective M p a b a' b' Hp Hq).
Qed.

Definition sf_invalid M (f : carrier M) : Prop :=
  exists a b,
    (f<>zeroM M /\ sf_tagged_graph M 0 a b f) \/
    ((sf_tagged_graph M 6 a b f \/ sf_tagged_graph M 7 a b f) /\ b<>zeroM M).

Definition sf_invalid_formula (f : pa_term) : pa_form :=
  ∃∃ (((¬ (code_lift2 f == zero)) ∧ sf_tagged_formula 0 $1 $0 (code_lift2 f)) ∨
    ((sf_tagged_formula 6 $1 $0 (code_lift2 f) ∨ sf_tagged_formula 7 $1 $0 (code_lift2 f)) ∧
      (¬ ($0 == zero)))).

Local Opaque holds sf_tagged_formula.

Theorem sf_invalid_formula_correct M rho f :
  holds M rho (sf_invalid_formula f) <-> sf_invalid M (evalM M rho f).
Proof.
  unfold sf_invalid_formula,sf_invalid.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_or.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_or.
  setoid_rewrite code_holds_neq. setoid_rewrite sf_tagged_formula_correct.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Theorem sf_invalid_definable M : Definable1 M (sf_invalid M).
Proof.
  exists (sf_invalid_formula $0),(fun _ => zeroM M).
  intro f. symmetry. apply sf_invalid_formula_correct.
Qed.

Theorem sf_code_cases M f :
  f=zeroM M \/ sf_invalid M f \/ exists h a b, sf_relation M h a b f.
Proof.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) f (zeroM M)) as [E|Hnz]; [now left|].
  right. destruct (sf_tagged_decomposition M f) as [tag [Htag [a [b H]]]].
  destruct tag as [|[|[|[|[|[|[|[|tag]]]]]]]]; try lia.
  - left. exists a,b. now left.
  - right. exists SFMember,a,b. now apply sf_relation_graph.
  - right. exists SFEqual,a,b. now apply sf_relation_graph.
  - right. exists SFAnd,a,b. now apply sf_relation_graph.
  - right. exists SFOr,a,b. now apply sf_relation_graph.
  - right. exists SFImpl,a,b. now apply sf_relation_graph.
  - destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) b (zeroM M)) as [E|Hbnz].
    + subst b. right. exists SFAll,a,(zeroM M). now apply sf_relation_graph.
    + left. exists a,b. right. auto.
  - destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) b (zeroM M)) as [E|Hbnz].
    + subst b. right. exists SFEx,a,(zeroM M). now apply sf_relation_graph.
    + left. exists a,b. right. auto.
Qed.

Theorem sf_invalid_not_zero M f : sf_invalid M f -> f<>zeroM M.
Proof.
  intros [a [b [[Hnz H]|[[H|H] Hbnz]]]] E; [exact (Hnz E)| |]; subst f.
  - destruct (sf_tagged_at_zero M 6 a b ltac:(lia) H) as [E _]. discriminate.
  - destruct (sf_tagged_at_zero M 7 a b ltac:(lia) H) as [E _]. discriminate.
Qed.

Theorem sf_invalid_not_constructor M h a b f :
  sf_invalid M f -> sf_relation M h a b f -> False.
Proof.
  intros [x [y [[Hnz Hbad]|[[Hbad|Hbad] Hynz]]]] Hgood;
    apply sf_relation_graph in Hgood.
  - destruct (sf_tagged_decode_unique M 0 (sf_tag h) x y a
      (sf_payload_second M h b) f ltac:(lia) (sf_tag_bound h) Hbad Hgood) as [E _].
    symmetry in E. exact (sf_tag_positive h E).
  - destruct (sf_tagged_decode_unique M 6 (sf_tag h) x y a
      (sf_payload_second M h b) f ltac:(lia) (sf_tag_bound h) Hbad Hgood) as [E [_ Ey]].
    destruct h; cbn in E; try discriminate. cbn in Ey. exact (Hynz Ey).
  - destruct (sf_tagged_decode_unique M 7 (sf_tag h) x y a
      (sf_payload_second M h b) f ltac:(lia) (sf_tag_bound h) Hbad Hgood) as [E [_ Ey]].
    destruct h; cbn in E; try discriminate. cbn in Ey. exact (Hynz Ey).
Qed.

Definition sf_binary (h : sf_head) : Prop := h=SFAnd \/ h=SFOr \/ h=SFImpl.
Definition sf_unary (h : sf_head) : Prop := h=SFAll \/ h=SFEx.

Theorem sf_code_induction M (P : carrier M -> Prop) :
  Definable1 M P -> P (zeroM M) ->
  (forall f, sf_invalid M f -> P f) ->
  (forall a b f, sf_relation M SFMember a b f -> P f) ->
  (forall a b f, sf_relation M SFEqual a b f -> P f) ->
  (forall h a b f, sf_binary h -> sf_relation M h a b f -> P a -> P b -> P f) ->
  (forall h a f, sf_unary h -> sf_relation M h a (zeroM M) f -> P a -> P f) ->
  forall f, P f.
Proof.
  intros HD Hzero Hinvalid Hmem Heq Hbinary Hunary.
  apply (definable_strong_induction M P HD). intros f IH.
  destruct (sf_code_cases M f) as [E|[Hbad|[h [a [b H]]]]].
  - now subst f.
  - now apply Hinvalid.
  - destruct (sf_relation_descent M h a b f H) as [Ha Hb].
    destruct h.
    + exact (Hmem a b f H).
    + exact (Heq a b f H).
    + apply (Hbinary SFAnd a b f); try assumption; try (unfold sf_binary; tauto).
      * exact (IH a Ha).
      * exact (IH b Hb).
    + apply (Hbinary SFOr a b f); try assumption; try (unfold sf_binary; tauto).
      * exact (IH a Ha).
      * exact (IH b Hb).
    + apply (Hbinary SFImpl a b f); try assumption; try (unfold sf_binary; tauto).
      * exact (IH a Ha).
      * exact (IH b Hb).
    + apply (Hunary SFAll a f); [unfold sf_unary; tauto|exact H|exact (IH a Ha)].
    + apply (Hunary SFEx a f); [unfold sf_unary; tauto|exact H|exact (IH a Ha)].
Qed.
