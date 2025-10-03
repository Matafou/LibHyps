Require Coq.Strings.String.
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr  Printf.
Import Constr.Unsafe.


Ltac2 rec length_constr_string (xs : constr) : int :=
  match kind xs with
  | App _ args =>
    match Int.equal (Array.length args) 2 with
    | true => Int.add 1 (length_constr_string (Array.get args 1))
    | _ => if equal xs 'String.EmptyString then 0 else Control.throw No_value
    end
  | Constr.Unsafe.Constructor _ _ => 0
  | _ => Control.throw No_value
  end.


Ltac2 string_of_constr_string (s : constr) : string :=
  let s := eval vm_compute in ($s : String.string) in
  let ret := String.make (length_constr_string s) (Char.of_int 0) in
  let t := constr:(true) in
  let rec fill i s :=
    match kind s with
    | App _ args =>
      if Int.equal (Array.length args) 2 then
        String.set ret i (match kind (Array.get args 0) with App _ b => Char.of_int (
            Int.add (if equal (Array.get b 0) t then 1 else 0) (
            Int.add (if equal (Array.get b 1) t then 2 else 0) (
            Int.add (if equal (Array.get b 2) t then 4 else 0) (
            Int.add (if equal (Array.get b 3) t then 8 else 0) (
            Int.add (if equal (Array.get b 4) t then 16 else 0) (
            Int.add (if equal (Array.get b 5) t then 32 else 0) (
            Int.add (if equal (Array.get b 6) t then 64 else 0) (
                    (if equal (Array.get b 7) t then 128 else 0)))))))))
          | _ => Control.throw No_value end);
        fill (Int.add i 1) (Array.get args 1)
      else ()
    | _ => ()
    end in
  fill 0 s; ret.

Ltac2 ident_of_constr_string (s : constr) := Option.get (Ident.of_string (string_of_constr_string s)).

Ltac2 eq_string s1 s2 := if String.equal s1 s2 then constr:(true) else constr:(false).

Ltac ident_of_constr_string_cps := ltac2:(s tac |-
  Ltac1.apply tac [Ltac1.of_ident (ident_of_constr_string (Option.get (Ltac1.to_constr s)))] Ltac1.run).

Ltac2 eq_id_string (id:ident) (s : string) :=
  if String.equal (Ident.to_string id) s then constr:(true) else constr:(false).

Ltac intro_as_string s := ident_of_constr_string_cps s ltac:(fun i => intro i).

Ltac evar_as_string s t := ident_of_constr_string_cps s ltac:(fun s => let s' := fresh s in evar(s':t)).

Ltac if_eqstr :=
  ltac2:(ident s tac1 tac2 |-
           (if String.equal
                 (Ident.to_string (Option.get (Ltac1.to_ident ident)))
                 (string_of_constr_string (Option.get (Ltac1.to_constr s)))
            then Ltac1.apply tac1 [] 
            else Ltac1.apply tac2 []) Ltac1.run).

Ltac2 is_dep_prod (h:ident) :=  
  let h := Control.hyp h in
  let th := Constr.type h in
  match Constr.Unsafe.kind th with
    | Prod _ c => Bool.neg (Constr.Unsafe.is_closed c)
    | _ => Control.zero (Tactic_failure (Some (fprintf "Not a product")))
  end.

Ltac2 rec chop_prod_until (th:constr) (id:ident): constr :=
  match Constr.Unsafe.kind th with
  | Prod bind th' =>
      (* Message.print (Message.of_constr th); *)
      match Binder.name bind with
      | None =>
          let res : constr := chop_prod_until th' id in
          Constr.Unsafe.make (Constr.Unsafe.Prod bind res)          
          
      | Some nme => 
          if Ident.equal nme id
          then Binder.type bind
          else
            let res : constr := chop_prod_until th' id in
            Constr.Unsafe.make (Constr.Unsafe.Prod bind res)          
      end
  | _ => Control.zero (Tactic_failure (Some (fprintf "Not a product")))
  end
.

Ltac2 Notation "chop" hyp(ident) "until" id(ident) :=
  let h := Control.hyp hyp in
  let th := Constr.type h in
  let res := chop_prod_until th id in
  Message.print (Message.of_constr res).



(*
Ltac2 analyze_deps (th:constr) (id:ident) :=
  match Constr.Unsafe.kind th with
  | Prod bind th' =>
      Message.print (Message.of_constr th);
      match Binder.name bind with
      | None =>  Message.print (Message.of_string "NO NAME")
      | Some nme => 
          if Ident.equal nme id
          then Message.print (Message.of_string "EQ")
          else
            if 
            Message.print (Message.of_string "NEQ")
      end
  | _ => Control.zero (Tactic_failure (Some (fprintf "Not a product")))
  end
.

Ltac2 Notation "deps" hyp(ident) "until" id(ident) :=
  let h := Control.hyp hyp in
  let th := Constr.type h in
  analyze_deps th id.
*)


(*
Set Default Proof Mode "Ltac2".
Goal (forall (n m p:nat) (hhh:n=p), m=1) -> (4=0 -> 1=1)-> 2=2 -> (forall m:nat, False).
  intros . 
  chop H until hhh.

  refinehd H.
*)


(*


Ltac2 Type specialize_arg :=
  [ QuantifArg | QuantifIgnoreArg | SubGoalArg | EvarArg(string)
  | QuantifUntilArg(string) | QuantifUntilNum(int) ].

Ltac2 Notation "is_depH" h(ident) := is_dep_prod h.

Ltac2 Notation "QuantifArg" := QuantifArg.

Ltac2 refine_hd (hyp:ident) (largs: specialize_arg list) (n:int) :=
  let h := Control.hyp hyp in
  let th := Constr.type h in
  match Constr.Unsafe.kind th with
  | Prod bind th' =>
      let newn:int := if Constr.Unsafe.is_closed th' then n else (Int.add n 1) in
      let x := Binder.name bind in
      let t := Binder.type bind in
      match largs with
      | QuantifArg :: largs' => 
          let hole := '_ in
          let open_cstr := Constr.Unsafe.make (Constr.Unsafe.Prod bind hole) in
          ltac1:(x |- refine x) (Ltac1.of_constr open_cstr)
          
                         
      | _ => Control.zero (Tactic_failure (Some (fprintf "Not implemented yet!")))
      end
  | _ =>
      match largs with
        [] => ltac1:(x |- exact x) (Ltac1.of_ident hyp)
      | _ => Control.zero (Tactic_failure (Some (fprintf "Not a product")))
      end
  end.



(* Ltac2 Notation refinehd := refine_hd. *)
Ltac2 Notation "refinehd" h(ident) := refine_hd h [QuantifArg] 0.
*)

(*
Set Default Proof Mode "Ltac2".


Goal (forall n, n=0 -> 1=1) -> (4=0 -> 1=1)-> 2=2 -> (forall m:nat, False).
  intros . 

  if (is_dep_prod ident:(H0)) then Message.print (Message.of_string "DEP")
  else Message.print (Message.of_string "NO DEP").

                          refinehd H.


  let newn := if is_dep_prod h then constr:(n) else (constr:(S n)) in
  

  lazymatch largs with
  | nil =>  exact h
  | _ => 
      lazymatch type of h with
      | (forall (x:?t) , _) =>
          lazymatch largs with
          | nil =>  exact h
          | cons QuantifArg ?largs' => 
              refine (fun x: t => _);
              specialize (h x);
              refine_hd h largs' newn
          | cons QuantifIgnoreArg ?largs' => 
              refine (fun x: t => _);
              specialize (h x);
              clear x;
              refine_hd h largs' newn
          | cons (QuantifUntilArg ?nme) ?largs' => 
              if_eqstr ident:(x) nme
              ltac:(idtac;refine_hd h (cons SubGoalArg largs') n)
              ltac:(idtac;refine_hd h (cons QuantifArg largs) n)
          | cons (QuantifUntilNum ?num) ?largs' => 
              if_is_dep_prod h
                ltac:((idtac;refine_hd h (cons QuantifArg largs) n))
                ltac:(idtac;tryif convert num newn
                             then refine_hd h (cons SubGoalArg largs') n
                             else refine_hd h (cons QuantifArg largs) n)
          | cons (EvarArg ?ename) ?largs' => 
              evar_as_string ename t;
              (* hackish: this should get the evar just created *)
              let hename := match goal with H:t|-_ => H end in
              specialize (h hename);
              subst hename;
              (* idtac "subst"; *)
              refine_hd h largs' newn
          | cons SubGoalArg ?largs' =>
              (unshelve evar_as_string "SubGoal" t);
              (* hackish: this should get the evar just created *)
              [ | let hename := match goal with
                                  H:t|-_ => H
                                end in
                  specialize (h hename);
                  subst hename;
                  (* idtac "subst"; *)
                  refine_hd h largs' newn]
          end
      | _ => idtac "Not enough products." ; fail
      end
  end.
*)

(*
(* Set Default Proof Mode "Classic". *)
 Set Default Proof Mode "Ltac2".
Goal (0=0 -> 1=1) -> 2=2 -> False.
  intros . 
  
  is_depH H.
  is_depH H0.

  let h := Control.hyp (Ident.of_string "H") in
  (is_dep_prod H).


  let t := type of H in
  lazy_match! t with
    (forall n:tn, reste) => Message.print (Message.of_string "Youhou")
  | _ => Message.print (Message.of_string "Buh")
  end.

  match! goal with
  | [ |- _ ] => 
      
      Control.plus (fun () => 
                      assert t;
                      Control.focus 1 1 (fun () => 
                                           let h := fresh "__h__" in
                                           intro h))
                   false
                   true

                match Control. with
                  
                end
                           (tryif clear h then fail 1 else fail)
  | [ |- _ ] => idtac
  end.

Ltac2 if_is_dep_prod H tac1 tac2 :=
  let t := type of H in
  match goal with
  | |- _ => match goal with
            | |- _ => assert t;
                      let h := fresh "__h__" in
                      intro h;
                      (tryif clear h then fail else fail 1) (* we fail in both cases to backtrack the assert*)
            | |- _ => tac2
            | |- _ => fail 2 (* don't fall back to tac1 *)
            end
  | |- _ => tac1
  end.
*)


(*
Goal forall toto:nat,True.
  intros toto.
  if_eqstr ident:(toto)


  let x := (Ident.to_string ident:(toto)) in
  if String.equal x "toti" then  Message.print (Message.of_string "true")
  else  Message.print (Message.of_string "false").

  Message.print (Message.of_string x);
  Message.print (Message.of_string "toto")
  .
  if String.equal x "toti" then  Message.print (Message.of_string "true")
  else Message.print (Message.of_string "true").

  let x := eq_id_string (Option.get (Ident.of_string "toto")) "toto" in
  Ltac1:(pose proof res).
*)

(*
Goal forall toto:nat,True.
  intros toto. 
  let x := eq_id_string (Option.get (Ident.of_string "toto")) "toto" in
  Ltac1:(pose proof res).*)

(*
Local Open Scope string_scope.
Local Set Default Proof Mode "Classic".
Import Coq.Strings.String Coq.Strings.Ascii. Local Open Scope string_scope.
Goal forall x:nat, True.
Proof.
  let s := constr:("ab_cdef_gh") in
  (* time *) do 1000 (intro_as_string s; revert ab_cdef_gh). (*0.5s*)
  let s := constr:("ab_cdef_gh") in
  intro_as_string s. 
Abort.

Local Set Warnings "-abstract-large-number".
Goal forall x:nat, True.
Proof.
  let s := eval vm_compute in (string_of_list_ascii (List.repeat "a"%char 10000)) in
  (* time *) intro_as_string s (*0.4s*).
Abort.

Goal forall x:nat, True.
Proof.
  let s := constr:("ab_cdef_gh") in
  evar_as_string s nat.
  ident_of_constr_string_cps s ltac:(fun x => let ev := open_constr:(x:nat) in
                                              assert (let x := ev in _)).
  let e := open_constr:(s:nat) in
  assert (e).

Abort.


*)
