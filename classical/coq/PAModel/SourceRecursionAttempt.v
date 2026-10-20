(** Literal varying-matrix recursion attempts. The binary relation matrix
    occupies its genuine input0/output1 roles under the fourth binder. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceFiniteCutoffShift
  SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport.
Unset Implicit Arguments.

Definition source_rec_attempt_zero M o a f out:=exists app equal point,
  source_rec_app M(succM M f)(succM M o)(zeroM M)app /\sf_relation M SFEqual(zeroM M)(succM M a)equal /\
  sf_relation M SFImpl app equal point /\sf_relation M SFAll point(zeroM M)out.
Definition rec_attempt_step_expression:=E_sf_all(E_sf_all(E_sf_all(E_sf SFImpl(CEvar 0)
  (E_sf SFImpl(CEvar 1)(E_sf SFImpl(CEvar 2)(E_sf_ex(E_sf SFAnd(CEvar 3)(CEvar 4)))))))).
Definition source_rec_env5 {A:Type}(a b c d e:A)(i:nat):=match i with 0=>a|1=>b|2=>c|3=>d|_=>e end.
Definition source_rec_attempt_step M phi N f out:=exists guard successor appOut appIn,
  sf_relation M SFMember(code_numeral M 2)(source_succ_iter M 3 N)guard /\
  source_rec_successor M(code_numeral M 2)(code_numeral M 1)successor /\
  source_rec_app M(source_succ_iter M 3 f)(code_numeral M 1)(zeroM M)appOut /\
  source_rec_app M(source_succ_iter M 4 f)(code_numeral M 3)(zeroM M)appIn /\
  code_relation M(source_rec_env5 guard successor appOut appIn phi)rec_attempt_step_expression out.
Definition source_rec_attempt M phi o a N f out:=exists first second,
  source_rec_attempt_zero M o a f first /\source_rec_attempt_step M phi N f second /\sf_relation M SFAnd first second out.

Theorem source_rec_attempt_zero_total M o a f:exists out,source_rec_attempt_zero M o a f out.
Proof.
  destruct(source_rec_app_total M(succM M f)(succM M o)(zeroM M)) as(app&HApp).
  destruct(sf_relation_total M SFEqual(zeroM M)(succM M a)) as(equal&HE).
  destruct(sf_relation_total M SFImpl app equal) as(point&HP).
  destruct(sf_relation_total M SFAll point(zeroM M)) as(out&HO). exists out,app,equal,point. auto.
Qed.
Theorem source_rec_attempt_zero_functional M o a f x y:
  source_rec_attempt_zero M o a f x ->source_rec_attempt_zero M o a f y ->x=y.
Proof.
  intros(app&equal&point&HA&HE&HP&HO)(app'&equal'&point'&HA'&HE'&HP'&HO').
  pose proof(source_rec_app_functional M(succM M f)(succM M o)(zeroM M)app' app HA' HA) as E. subst app'.
  pose proof(sf_relation_functional M SFEqual(zeroM M)(succM M a)equal' equal HE' HE) as E. subst equal'.
  pose proof(sf_relation_functional M SFImpl app equal point' point HP' HP) as E. subst point'.
  exact(sf_relation_functional M SFAll point(zeroM M)x y HO HO').
Qed.
Theorem source_rec_attempt_step_total M phi N f:exists out,source_rec_attempt_step M phi N f out.
Proof.
  destruct(sf_relation_total M SFMember(code_numeral M 2)(source_succ_iter M 3 N)) as(guard&HG).
  destruct(source_rec_successor_total M(code_numeral M 2)(code_numeral M 1)) as(successor&HS).
  destruct(source_rec_app_total M(source_succ_iter M 3 f)(code_numeral M 1)(zeroM M)) as(appOut&HO).
  destruct(source_rec_app_total M(source_succ_iter M 4 f)(code_numeral M 3)(zeroM M)) as(appIn&HI).
  destruct(code_relation_total M rec_attempt_step_expression(source_rec_env5 guard successor appOut appIn phi)) as(out&HF).
  exists out,guard,successor,appOut,appIn. auto.
Qed.
Theorem source_rec_attempt_step_functional M phi N f x y:
  source_rec_attempt_step M phi N f x ->source_rec_attempt_step M phi N f y ->x=y.
Proof.
  intros(guard&successor&appOut&appIn&HG&HS&HO&HI&HF)(guard'&successor'&appOut'&appIn'&HG'&HS'&HO'&HI'&HF').
  pose proof(sf_relation_functional M SFMember(code_numeral M 2)(source_succ_iter M 3 N)guard' guard HG' HG) as E. subst guard'.
  pose proof(source_rec_successor_functional M(code_numeral M 2)(code_numeral M 1)successor' successor HS' HS) as E. subst successor'.
  pose proof(source_rec_app_functional M(source_succ_iter M 3 f)(code_numeral M 1)(zeroM M)appOut' appOut HO' HO) as E. subst appOut'.
  pose proof(source_rec_app_functional M(source_succ_iter M 4 f)(code_numeral M 3)(zeroM M)appIn' appIn HI' HI) as E. subst appIn'.
  exact(code_relation_functional M rec_attempt_step_expression(source_rec_env5 guard successor appOut appIn phi)x y HF HF').
Qed.
Theorem source_rec_attempt_total M phi o a N f:exists out,source_rec_attempt M phi o a N f out.
Proof.
  destruct(source_rec_attempt_zero_total M o a f) as(first&HF).
  destruct(source_rec_attempt_step_total M phi N f) as(second&HS).
  destruct(sf_relation_total M SFAnd first second) as(out&HO). exists out,first,second. auto.
Qed.
Theorem source_rec_attempt_functional M phi o a N f x y:
  source_rec_attempt M phi o a N f x ->source_rec_attempt M phi o a N f y ->x=y.
Proof.
  intros(first&second&HF&HS&HO)(first'&second'&HF'&HS'&HO').
  pose proof(source_rec_attempt_zero_functional M o a f first' first HF' HF) as E. subst first'.
  pose proof(source_rec_attempt_step_functional M phi N f second' second HS' HS) as E. subst second'.
  exact(sf_relation_functional M SFAnd first second x y HO HO').
Qed.

Print Assumptions source_rec_attempt_zero_total.
Print Assumptions source_rec_attempt_zero_functional.
Print Assumptions source_rec_attempt_step_total.
Print Assumptions source_rec_attempt_step_functional.
Print Assumptions source_rec_attempt_total.
Print Assumptions source_rec_attempt_functional.
