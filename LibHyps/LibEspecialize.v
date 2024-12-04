Require Import Arith.
(* The tactics in this file use the folowing pattern, that consists in
   refining a new evar goal until being in the right scope to prove
   the premise. *)
(* 
Lemma foo: forall x y : nat, (forall n m p :nat, n < m -> n <= m -> p > 0 -> False) -> False.
Proof.
  intros x y H. 
  (* On veut prouver le n <= m comme conséquence du n < m dans H. *)
  (* On crée un but dont le type n'est pas connu, et on raffine pour
     être dans le bon environnement. *)
  let ev := open_constr:(_) in
  assert (ev) as h.
  { refine (fun (n m p:nat) (h:n < m) => _).
    assert(n <= m) as hhyp.
    { now apply Nat.lt_le_incl. }
    exact(H n m p h hhyp). }
  (* Voilà! *)
Admitted.
*)  

(* Describing how each arg of a hypothesis must be treated: either
   requantify it, or evarize it, or requantify but don't use it in
   premise proofs (not sure this is needed). We don't use list for
   cosmetic reasons: no need for nil (since the list is non empty),
   and avoid using lists. *)
Inductive spec_args : Type :=
  ConsQuantif: spec_args -> spec_args
| ConsEvar: spec_args -> spec_args
| ConsIgnore: spec_args -> spec_args
| ConsSubGoal: spec_args -> spec_args
| SubGoalEnd: spec_args.

(* List storing heterogenous terms, for storing (tele(scopes). A
   simple product could also be used. *)
Inductive Depl :=
| DNil: Depl
| DCons: forall (A:Type) (x:A), Depl -> Depl.

Declare Scope specialize_scope.
Delimit Scope specialize_scope with spec.
Local Open Scope specialize_scope.


(* builds the application of c to each element of l (in reversed
   order). apply t [t1;t2;t3] => (t t3 t2 t1) *)
Ltac list_apply c l :=
  match l with
    DNil => c
  | DCons _ ?x ?l' =>
      let inside := list_apply c l' in
      let res := constr:(ltac:(exact (inside x))) in
      res
  end.

(* - We start from a goal evar EV with no typing constraint.

    h: forall x y z, P x -> ...
    ========================
    ?EV

    subgoal 2
    h: forall x y z, P x -> ...
    ========================
    old goal
    

  - We refine is to have the same products at head than h, until we
    reach the aimed hypothesis

    h: P x -> ...
    x: ...   y: ...   z: ...
    ========================
    ?EV

  - then we do 2 things
    - create a goal USERGOAL for this hyp
    - conclude EV (and fix its type) by applying h to USERGOAL

    subgoal 1
    x: ...   y: ...   z: ...
    ==========================
    P x

    subgoal 2:
    h: forall x y z, P x -> ...
    hEV: forall x y z, ...
    ==========================
    old goal

   Refines a non specified goal (an evar) to prove the specialized
   version of h. The idea is to use (fun x y z => (?ev x y z)) as the
   argument being instnaciated, where ?ev will be the new goal

 larg is the specidication of what to do with each arg, larg2 is the
   accumulator *)
Ltac refine_hd h largs largs2 :=
  match largs with
  | SubGoalEnd => match type of h with
                  | (forall x:?t, _) =>
                      let h' := fresh h in
                      (* create the user subgoal *)
                      assert(t) as h'
                      ;[ clear h
                       | exact (h h')
                         (*let res := list_apply h' largs2 in
                  exact (h res) *) ]  
                  end
  | ConsQuantif ?largs' => 
      match type of h with
      | (forall x:?t, _) =>
          (* let y:= fresh x in *)
          (* intro y; *)
          refine (fun x: t => _);
          specialize (h x);
          refine_hd h largs' constr:(DCons _ x largs2)
      end
  | ConsEvar ?largs' => 
      match type of h with
      | (forall x:?t, _) =>
          (* morally this evar is of type t, don't know how to enforce this
             without having an ugly cast in goals *)
          let ev1 := open_constr:(_:t) in
          refine (let x:= ev1 in _);
          specialize (h x);
          subst x;
          refine_hd h largs' largs2
      end
  | ConsSubGoal?largs' => match type of h with
                          | (forall x:?t, _) =>
                              let h' := fresh h in
                              (* create the user subgoal *)
                              assert(t) as h'
                              ;[ clear h
                               | exact (h h')
                                 (*let res := list_apply h' largs2 in
                                   exact (h res) *) ]   
                          end
  end.

(* Precondition: name is already fresh *)
Global Ltac espec_gen H l name :=
  (* let l := eval cbn [spec_interp] in (spec_interp args) in   *)
  (* let h := fresh name in *)
  (* morally this evar is of type Type, don't know how to enforce this
     without having an ugly cast in goals *)
  let ev1 := open_constr:(_) in
  assert ev1 as name
  ; [
      (refine_hd H l DNil)
    | ].
  
Global Ltac especialize_clear H args :=
  let temp := fresh H "temp" in
  espec_gen H args temp;
  [ | clear H;
      idtac "ICI: " temp;
      rename temp into H ].

Global Ltac especialize_autoname H args :=
  let name := fresh H "_inst" in
  espec_gen H args name.

Global Ltac especialize_clear_autoname H args :=
  let name := fresh H "_inst" in
  especialize_autoname H args name.

Module SpecNotation.
  (* Notation "![ ]!" := DNil (format "![ ]!") : specialize_scope. *)
  (* Notation "![ x ]!" := (DCons _ x nil) : specialize_scope. *)
  (* Notation "![ x ; y ; .. ; z ]!" := *)
    (* (DCons _ x (DCons _ y .. (DCons _ z DNil) ..)) *)
      (* (format "![ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]!") : specialize_scope. *)
  Notation "! X" := (ConsQuantif X) (at level 100) : specialize_scope.
  Notation "? X" := (ConsEvar X) (at level 100) : specialize_scope.
  Notation "# X" := (ConsSubGoal X) (at level 100) : specialize_scope.
  Notation "#" := (SubGoalEnd) (at level 100) : specialize_scope.
Module SpecNotation.

Tactic Notation "especialize" constr(H) "at" constr(specarg) "as" ident(idH) :=
  espec_gen H specarg idH.
Tactic Notation "especialize"  constr(specarg) "as" constr(H) "at" ident(idH) :=
  espec_gen H specarg idH.

Tactic Notation "especialize" constr(H) "at" constr(specarg) :=
  especialize_clear H specarg.




Definition eq_one (i:nat) := i = 1.


Lemma test_espec: forall x:nat, (forall y:nat,eq_one 2 -> eq_one 3 -> eq_one y -> x=0 -> False) -> True.
Proof.
  intros x h_eqone.
  (* let nme := fresh_robust H "hh" "def" in idtac nme.Definition *)
  
  especialize h_eqone at (?#) as newH.
    [ admit | ].  match type of newH with (eq_one 2 -> eq_one y -> x = 0 -> False) => idtac end;
              match type of h_eqone with forall y : nat, eq_one 2 -> eq_one 3 -> eq_one y -> x = 0 -> False => idtac end].
  Undo.
  especialize h_eqone at (!!#) as newH;
    [ admit | match type of newH with (forall y : nat, eq_one 2 -> eq_one y -> x = 0 -> False) => idtac end;
              match type of h_eqone with forall y : nat, eq_one 2 -> eq_one 3 -> eq_one y -> x = 0 -> False => idtac end].
  Undo.
  especialize h_eqone at (!#) as newH
  ;[ admit
   |  match type of newH with  forall y : nat, eq_one 3 -> eq_one y ->  x = 0 -> False => idtac end;
        match type of h_eqone with forall y : nat, eq_one 2 -> eq_one 3 -> eq_one y -> x = 0 -> False => idtac end].

  Undo.
  especialize h_eqone at (!!!#) as newH;
    [ admit | match type of newH with  nat -> eq_one 2 -> eq_one 3 -> x = 0 -> False => idtac end;
                match type of h_eqone with forall y : nat, eq_one 2 -> eq_one 3 -> eq_one y -> x = 0 -> False => idtac end].
  Undo.


Lemma test_espec: (eq_one 2 -> eq_one 3 -> eq_one 1 -> False) -> True.
Proof.
  intros h_eqone.


  (* let nme := fresh_robust H "hh" "def" in idtac nme.Definition *)
  pose (c:= !!?#).
  pose (c:= !!?#!#).
  especialize h_eqone at (!#) as newH;
    [ admit | match type of newH with eq_one 2 -> eq_one 1 -> False => idtac end;
              match type of h_eqone with  eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac end].
  Undo.
  especialize h_eqone at (?) as newH
  ;[ admit
       | match type of newH with  eq_one 3 -> eq_one 1 -> False => idtac end;
         match type of h_eqone with  eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac end].

  Undo.
  especialize h_eqone at (!!#) as newH;
    [ admit | match type of newH with eq_one 2 -> eq_one 3 -> False => idtac end;
              match type of h_eqone with  eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac end].



  especialize (let x:=Nat.le_antisymm in x) at 2 as hhh;
    [ admit | match type of hhh with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize (let x:=Nat.le_antisymm in x)as hhh at 2;
    [ admit | match type of hhh with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize h_eqone at 2;
    [ admit | match type of h_eqone with eq_one 2 -> eq_one 1 -> False => idtac end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2;
    [ admit | match goal with |- (_ <= _ -> _ = _) -> True => idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize h_eqone as ? at 2;
    [ admit | match type of h_eqone_spec with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone at 2 as ? ;
    [ admit | match type of h_eqone_spec with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  
  especialize (let x:=Nat.le_antisymm in x) as ? at 2;
    [ admit | match type of H_spec with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2 as ? ;
    [ admit | match type of H_spec with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
