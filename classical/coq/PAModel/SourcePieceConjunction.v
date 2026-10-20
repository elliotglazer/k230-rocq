(** Internally finite PCf conjunctions over beta-coded (K,b) pieces.
    Both the number of pieces and each parameter count may be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  Pairing InternalRecursion ProofClosure SourcePieceClosure SourcePieceClosureFacts SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_piece_conjunction_step M domain level sb sc d X b c n v:=
  (n=zeroM M /\sf_relation M SFImpl(zeroM M)(zeroM M)v) \/
  exists k previous entry count phi pc,n=succM M k /\beta M b c k previous /\beta M sb sc k entry /\
    pair_graph M count phi entry /\source_pc_instance M domain level count phi d X pc /\
    sf_relation M SFAnd previous pc v.

Definition source_piece_conjunction_step_formula:form:=
  (($1==zero) ∧sf_formula SFImpl zero zero $0) ∨
  ∃∃∃∃∃∃($7==σ $5 ∧beta_formula $9 $8 $5 $4 ∧beta_formula $12 $13 $5 $3 ∧
    pair_formula $2 $1 $3 ∧source_pc_instance_formula $10 $11 $2 $1 $14 $15 $0 ∧sf_formula SFAnd $4 $0 $6).
Local Opaque beta_formula sf_formula source_pc_instance_formula.

Lemma source_piece_conjunction_step_correct M rho b c n v:
  recursion_step M source_piece_conjunction_step_formula rho b c n v <->
  source_piece_conjunction_step M(rho 0)(rho 1)(rho 2)(rho 3)(rho 4)(rho 5)b c n v.
Proof.
  unfold recursion_step,source_piece_conjunction_step_formula,source_piece_conjunction_step.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite pair_formula_correct. setoid_rewrite source_pc_instance_formula_correct.
  change (((n=zeroM M /\sf_relation M SFImpl(zeroM M)(zeroM M)v) \/
    exists k p entry count phi pc,
      (((((n=succM M k /\beta M b c k p) /\beta M(rho 2)(rho 3)k entry) /\pair_graph M count phi entry) /\
      source_pc_instance M(rho 0)(rho 1)count phi(rho 4)(rho 5)pc) /\sf_relation M SFAnd p pc v)) <->
    ((n=zeroM M /\sf_relation M SFImpl(zeroM M)(zeroM M)v) \/
    exists k p entry count phi pc,n=succM M k /\beta M b c k p /\beta M(rho 2)(rho 3)k entry /\
      pair_graph M count phi entry /\source_pc_instance M(rho 0)(rho 1)count phi(rho 4)(rho 5)pc /\
      sf_relation M SFAnd p pc v)).
  split;intros[H|(k&p&entry&count&phi&pc&H)];[now left|right;exists k,p,entry,count,phi,pc;tauto|
    now left|right;exists k,p,entry,count,phi,pc;tauto].
Qed.

Lemma source_piece_conjunction_step_total M domain level sb sc d X b c n:
  exists v,source_piece_conjunction_step M domain level sb sc d X b c n v.
Proof.
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)n)
    as[->|[k ->]].
  - destruct(sf_relation_total M SFImpl(zeroM M)(zeroM M)) as(v&HV). exists v. now left.
  - destruct(beta_total M b c k) as(p&HP). destruct(beta_total M sb sc k) as(entry&HE).
    destruct(pair_surjective M entry) as(count&phi&HC).
    destruct(source_pc_instance_total M domain level count phi d X) as(pc&HPC).
    destruct(sf_relation_total M SFAnd p pc) as(v&HV).
    exists v. right. exists k,p,entry,count,phi,pc. auto 10.
Qed.

Lemma source_piece_conjunction_step_functional M domain level sb sc d X b c n v w:
  source_piece_conjunction_step M domain level sb sc d X b c n v ->
  source_piece_conjunction_step M domain level sb sc d X b c n w ->v=w.
Proof.
  intros[[E HV]|(k&p&entry&count&phi&pc&E&HP&HE&HC&HPC&HV)]
    [[E' HW]|(k'&p'&entry'&count'&phi'&pc'&E'&HP'&HE'&HC'&HPC'&HW)].
  - exact(sf_relation_functional M SFImpl(zeroM M)(zeroM M)v w HV HW).
  - exfalso. apply(zero_ne_succ M k'). congruence.
  - exfalso. apply(zero_ne_succ M k). congruence.
  - assert(k=k') by(apply(succ_injective M);congruence). subst k'.
    pose proof(beta_unique M b c k p p' HP HP') as E0. subst p'.
    pose proof(beta_unique M sb sc k entry entry' HE HE') as E0. subst entry'.
    destruct(pair_injective M entry count phi count' phi' HC HC') as[E0 E1]. subst count' phi'.
    pose proof(source_pc_instance_functional M domain level count phi d X pc pc' HPC HPC') as E0. subst pc'.
    exact(sf_relation_functional M SFAnd p pc v w HV HW).
Qed.

Lemma source_piece_conjunction_step_prefix M domain level sb sc d X b c b' c' n:
  prefix M b c b' c' n ->forall v,
  (source_piece_conjunction_step M domain level sb sc d X b c n v <->
    source_piece_conjunction_step M domain level sb sc d X b' c' n v).
Proof.
  intros HPre v. split;intros[H|(k&p&entry&count&phi&pc&->&HP&HE&HC&HPC&HV)].
  - now left.
  - right. exists k,p,entry,count,phi,pc. split;[reflexivity|]. split;[|auto 10].
    exact(HPre k p(coding_lt_succ M k)HP).
  - now left.
  - right. exists k,p,entry,count,phi,pc. split;[reflexivity|]. split;[|auto 10].
    exact(prefix_back M b c b' c'(succM M k)HPre k p(coding_lt_succ M k)HP).
Qed.

Definition source_piece_conjunction M domain level sb sc n d X result:=exists b c,
  (forall i v,coding_lt M i(succM M n) ->beta M b c i v ->
    source_piece_conjunction_step M domain level sb sc d X b c i v) /\beta M b c n result.

Lemma source_piece_conjunction_recursion M rho n result:
  recursion_graph M source_piece_conjunction_step_formula rho n result <->
  source_piece_conjunction M(rho 0)(rho 1)(rho 2)(rho 3)n(rho 4)(rho 5)result.
Proof.
  unfold recursion_graph,recursion_prefix,source_piece_conjunction.
  setoid_rewrite source_piece_conjunction_step_correct. reflexivity.
Qed.

Theorem source_piece_conjunction_total M domain level sb sc n d X:
  exists result,source_piece_conjunction M domain level sb sc n d X result.
Proof.
  set(rho:=domain.:level.:sb.:sc.:d.:X.:fun _=>zeroM M).
  assert(HT:forall b c i,exists v,recursion_step M source_piece_conjunction_step_formula rho b c i v).
  { intros b c i. setoid_rewrite source_piece_conjunction_step_correct. apply source_piece_conjunction_step_total. }
  assert(HP:forall b c b' c' i,prefix M b c b' c' i ->forall v,
    (recursion_step M source_piece_conjunction_step_formula rho b c i v <->
      recursion_step M source_piece_conjunction_step_formula rho b' c' i v)).
  { intros b c b' c' i HPre v. repeat setoid_rewrite source_piece_conjunction_step_correct.
    exact(source_piece_conjunction_step_prefix M domain level sb sc d X b c b' c' i HPre v). }
  destruct(recursion_graph_total M source_piece_conjunction_step_formula rho HT HP n) as(v&HV).
  exists v. exact(proj1(source_piece_conjunction_recursion M rho n v)HV).
Qed.

Theorem source_piece_conjunction_functional M domain level sb sc n d X f g:
  source_piece_conjunction M domain level sb sc n d X f ->
  source_piece_conjunction M domain level sb sc n d X g ->f=g.
Proof.
  set(rho:=domain.:level.:sb.:sc.:d.:X.:fun _=>zeroM M).
  assert(HF:forall b c i v w,recursion_step M source_piece_conjunction_step_formula rho b c i v ->
    recursion_step M source_piece_conjunction_step_formula rho b c i w ->v=w).
  { intros b c i v w. repeat setoid_rewrite source_piece_conjunction_step_correct.
    apply source_piece_conjunction_step_functional. }
  assert(HP:forall b c b' c' i,prefix M b c b' c' i ->forall v,
    (recursion_step M source_piece_conjunction_step_formula rho b c i v <->
      recursion_step M source_piece_conjunction_step_formula rho b' c' i v)).
  { intros b c b' c' i HPre v. repeat setoid_rewrite source_piece_conjunction_step_correct.
    exact(source_piece_conjunction_step_prefix M domain level sb sc d X b c b' c' i HPre v). }
  change(source_piece_conjunction M(rho 0)(rho 1)(rho 2)(rho 3)n(rho 4)(rho 5)f ->
    source_piece_conjunction M(rho 0)(rho 1)(rho 2)(rho 3)n(rho 4)(rho 5)g ->f=g).
  rewrite <-!source_piece_conjunction_recursion.
  exact(recursion_graph_functional M source_piece_conjunction_step_formula rho HF HP n f g).
Qed.

Theorem source_piece_conjunction_zero M domain level sb sc d X result:
  source_piece_conjunction M domain level sb sc(zeroM M)d X result <->
  sf_relation M SFImpl(zeroM M)(zeroM M)result.
Proof.
  assert(Forward:forall result,source_piece_conjunction M domain level sb sc(zeroM M)d X result ->
    sf_relation M SFImpl(zeroM M)(zeroM M)result).
  { intros f(b&c&HSteps&HR).
    destruct(HSteps(zeroM M)f(coding_lt_succ M(zeroM M))HR) as[[_ H]|(k&p&entry&count&phi&pc&E&_)];[exact H|].
    exfalso. exact(zero_ne_succ M k E). }
  split;[apply Forward|intro H].
  destruct(source_piece_conjunction_total M domain level sb sc(zeroM M)d X) as(f&HF).
  pose proof(sf_relation_functional M SFImpl(zeroM M)(zeroM M)f result(Forward f HF)H) as E. now subst result.
Qed.

Theorem source_piece_conjunction_succ M domain level sb sc n d X result:
  source_piece_conjunction M domain level sb sc(succM M n)d X result <->
  exists previous entry count phi pc,source_piece_conjunction M domain level sb sc n d X previous /\
    beta M sb sc n entry /\pair_graph M count phi entry /\source_pc_instance M domain level count phi d X pc /\
    sf_relation M SFAnd previous pc result.
Proof.
  assert(Forward:forall result,source_piece_conjunction M domain level sb sc(succM M n)d X result ->
    exists p entry count phi pc,source_piece_conjunction M domain level sb sc n d X p /\
      beta M sb sc n entry /\pair_graph M count phi entry /\source_pc_instance M domain level count phi d X pc /\
      sf_relation M SFAnd p pc result).
  { intros f(b&c&HSteps&HR).
    destruct(HSteps(succM M n)f(coding_lt_succ M(succM M n))HR)
      as[[E _]|(k&p&entry&count&phi&pc&E&HP&HE&HC&HPC&HV)].
    - exfalso. apply(zero_ne_succ M n). symmetry. exact E.
    - assert(n=k) by(apply(succ_injective M);exact E). subst k.
      exists p,entry,count,phi,pc. split;[|auto]. exists b,c. split;[|exact HP].
      intros i v HI HV'. apply HSteps;[|exact HV']. apply coding_lt_succ_cases. now left. }
  split;[apply Forward|intros(p&entry&count&phi&pc&HP&HE&HC&HPC&HV)].
  destruct(source_piece_conjunction_total M domain level sb sc(succM M n)d X) as(f&HF).
  destruct(Forward f HF) as(p'&entry'&count'&phi'&pc'&HP'&HE'&HC'&HPC'&HV').
  pose proof(source_piece_conjunction_functional M domain level sb sc n d X p' p HP' HP) as E. subst p'.
  pose proof(beta_unique M sb sc n entry' entry HE' HE) as E. subst entry'.
  destruct(pair_injective M entry count' phi' count phi HC' HC) as[E E']. subst count' phi'.
  pose proof(source_pc_instance_functional M domain level count phi d X pc' pc HPC' HPC) as E. subst pc'.
  pose proof(sf_relation_functional M SFAnd p pc f result HV' HV) as E. now subst result.
Qed.

Print Assumptions source_piece_conjunction_total.
Print Assumptions source_piece_conjunction_functional.
Print Assumptions source_piece_conjunction_zero.
Print Assumptions source_piece_conjunction_succ.
