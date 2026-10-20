(** Fixed hierarchy and equality laws used under the fresh level-set
    binder of the positive witness request. Both laws have actual ZFR proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceHierarchyWitnessShell SourceMemberEquality SourceZFRProvability SourceDescriptorProvability
  SourceDescriptorClosure SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_positive_witness_plan M d y carrier allUnique allMove :=
  exists od ld le equal t1 t2 unique oldMember newMember moveImp move,
    source_hierarchy_unique_shell M(succM M d)(succM M carrier)(zeroM M)od ld le equal t1 t2 unique /\
    sf_relation M SFMember(succM M y)(succM M carrier)oldMember /\
    sf_relation M SFMember(succM M y)(zeroM M)newMember /\
    sf_relation M SFImpl oldMember newMember moveImp /\sf_relation M SFImpl equal moveImp move /\
    sf_relation M SFAll unique(zeroM M)allUnique /\sf_relation M SFAll move(zeroM M)allMove.

Theorem source_positive_witness_plan_total M d y carrier :exists allUnique allMove,
  source_positive_witness_plan M d y carrier allUnique allMove /\
  source_zfr_provable M allUnique /\source_zfr_provable M allMove.
Proof.
  destruct(source_zfr_hierarchy_unique_shell M(succM M d)(succM M carrier)(zeroM M))
    as(od&ld&le&equal&t1&t2&unique&HUnique&PUnique).
  set(rho:=fun i=>match i with 0=>succM M y|1=>succM M carrier|_=>zeroM M end).
  destruct(code_relation_total M source_member_right_equality_expression rho) as(move&HMove).
  pose proof(source_zfr_member_right_equality M rho move HMove) as PMove.
  destruct(source_member_right_equality_shell M rho move HMove)
    as(equal'&oldMember&newMember&moveImp&HE&HOld&HNew&HMoveImp&HMoveCode).
  destruct HUnique as(HOrd&HLD&HLE&HEqual&HT2&HT1&HU).
  pose proof(sf_relation_functional M SFEqual(succM M carrier)(zeroM M)equal' equal HE HEqual) as E.
  subst equal'.
  destruct(sf_relation_total M SFAll unique(zeroM M)) as(allUnique&HAU).
  destruct(sf_relation_total M SFAll move(zeroM M)) as(allMove&HAM).
  exists allUnique,allMove. split.
  - exists od,ld,le,equal,t1,t2,unique,oldMember,newMember,moveImp,move.
    split;[repeat split;assumption|]. repeat split;assumption.
  - split.
    + apply(proj1(source_zfr_descriptor_provable M allUnique)).
      exact(source_descriptor_provable_all M ZFRSourceDescriptor unique allUnique
        (proj2(source_zfr_descriptor_provable M unique)PUnique)HAU).
    + apply(proj1(source_zfr_descriptor_provable M allMove)).
      exact(source_descriptor_provable_all M ZFRSourceDescriptor move allMove
        (proj2(source_zfr_descriptor_provable M move)PMove)HAM).
Qed.

Print Assumptions source_positive_witness_plan_total.
