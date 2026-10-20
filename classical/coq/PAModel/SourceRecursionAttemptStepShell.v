(** Literal constructors of the three-quantifier attempt-step clause and
    of its predecessor-value existential conclusion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceFiniteCutoffShift
  SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionAttempt SourceRecursionBinaryInstance SourceFunctionalityShells.
Unset Implicit Arguments.

Theorem source_rec_attempt_step_shell M phi N f out:
  source_rec_attempt_step M phi N f out ->exists guard successor appOut appIn body ex t3 t2 point one two,
    sf_relation M SFMember(code_numeral M 2)(source_succ_iter M 3 N)guard /\
    source_rec_successor M(code_numeral M 2)(code_numeral M 1)successor /\
    source_rec_app M(source_succ_iter M 3 f)(code_numeral M 1)(zeroM M)appOut /\
    source_rec_app M(source_succ_iter M 4 f)(code_numeral M 3)(zeroM M)appIn /\
    sf_relation M SFAnd appIn phi body /\sf_relation M SFEx body(zeroM M)ex /\
    sf_relation M SFImpl appOut ex t3 /\sf_relation M SFImpl successor t3 t2 /\sf_relation M SFImpl guard t2 point /\
    sf_relation M SFAll point(zeroM M)one /\sf_relation M SFAll one(zeroM M)two /\sf_relation M SFAll two(zeroM M)out.
Proof.
  intros(guard&successor&appOut&appIn&HG&HS&HO&HI&HOut).
  destruct(sf_relation_total M SFAnd appIn phi) as(body&HB).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(ex&HE).
  destruct(sf_relation_total M SFImpl appOut ex) as(t3&H3).
  destruct(sf_relation_total M SFImpl successor t3) as(t2&H2).
  destruct(sf_relation_total M SFImpl guard t2) as(point&HP).
  destruct(sf_relation_total M SFAll point(zeroM M)) as(one&H1).
  destruct(sf_relation_total M SFAll one(zeroM M)) as(two&H2A).
  destruct(sf_relation_total M SFAll two(zeroM M)) as(target&HF).
  assert(HOut':code_relation M(source_rec_env5 guard successor appOut appIn phi)rec_attempt_step_expression target).
  { unfold rec_attempt_step_expression,SetSchemaConstructors.E_sf_all,SetSchemaConstructors.E_sf_ex. functionality_graph. }
  pose proof(code_relation_functional M rec_attempt_step_expression(source_rec_env5 guard successor appOut appIn phi)out target HOut HOut') as E. subst target.
  exists guard,successor,appOut,appIn,body,ex,t3,t2,point,one,two. auto 15.
Qed.

Definition source_rec_transition_witness M phi f u v out:=exists app binary body,
  source_rec_app M(succM M f)(succM M u)(zeroM M)app /\source_rec_binary M phi(zeroM M)(succM M v)binary /\
  sf_relation M SFAnd app binary body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_rec_transition_witness_total M phi f u v:exists out,source_rec_transition_witness M phi f u v out.
Proof.
  destruct(source_rec_app_total M(succM M f)(succM M u)(zeroM M)) as(app&HApp).
  destruct(source_rec_binary_total M phi(zeroM M)(succM M v)) as(binary&HBinary).
  destruct(sf_relation_total M SFAnd app binary) as(body&HB).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(out&HE). exists out,app,binary,body. auto.
Qed.
Theorem source_rec_transition_witness_functional M phi f u v a b:
  source_rec_transition_witness M phi f u v a ->source_rec_transition_witness M phi f u v b ->a=b.
Proof.
  intros(app&binary&body&HApp&HBinary&HB&HE)(app'&binary'&body'&HApp'&HBinary'&HB'&HE').
  pose proof(source_rec_app_functional M(succM M f)(succM M u)(zeroM M)app' app HApp' HApp) as E. subst app'.
  pose proof(source_rec_binary_functional M phi(zeroM M)(succM M v)binary' binary HBinary' HBinary) as E. subst binary'.
  pose proof(sf_relation_functional M SFAnd app binary body' body HB' HB) as E. subst body'.
  exact(sf_relation_functional M SFEx body(zeroM M)a b HE HE').
Qed.

Print Assumptions source_rec_attempt_step_shell.
Print Assumptions source_rec_transition_witness_total.
Print Assumptions source_rec_transition_witness_functional.
