Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.
Import Constr.Unsafe.
Local Set Default Proof Mode "Classic".
(* Require Import LibHyps.LibHypsDebug. *)

(* Utilities *)
Local Ltac2 is_dep_prod (t:constr): bool :=
  match kind t with
  | Prod _ subt => Bool.neg (is_closed subt)
  | _ => false
  end.

Local Ltac2 pr_list (pr: unit -> 'a -> message) () (l: 'a list) :=
  let rec pr_list_  () (l: 'a list) :=
    match l with
    | [] => fprintf ""
    | [e] => fprintf "%a" pr e
    | e::l' => fprintf "%a , %a" pr e pr_list_ l'
    end in
  fprintf "[ %a ]" pr_list_ l.


(* ESPECIALIZE INTERNAL DOC *)
(* We show here by hand what the especialize tactic does. We start
with a hypothesis H of type

H: (forall n m:nat, n<m -> n<=m -> forall p:nat, p>0 -> p+1 = m+n)

Suppose we want:

1. let the user prove that the premise (n <= m) can be proved from the
   other premise (n < m) and can thus be removed from H

2. let the user prove the premise (p > 0) for a p yet to be determined
   (evar) and remove both p and (p>0) from H.
*)
Lemma foo: forall x y : nat, (forall n m:nat, n < m -> n <= m -> forall p:nat, p > 0 -> p+1 = m+n) -> False.
Proof.

  intros x y H. 
  (* - We start from a goal evarEV with no typing constraint. *)
  let ev1 := open_constr:(_) in
  assert ev1 as newH.
  (* then we refine this unknown goal by mimick H until we reach the
  premise we want to remove: *)
  intro n. (*or refine (fun (n:nat) => _) *)
  specialize (H n).
  intro m. 
  specialize (H m).

  (* 1 more times, but more automatic *)
  match type of H with
    (forall nme:?t, _) => (intro nme) (*refine (fun nme:t => _)*); specialize (H nme)
  end.
  
  (* We want to prove (n<=m) as a consequence of (n<m) in H. So here
  instead of mimickig H we assert the premise as a new goal. *)
  assert (n<=m) as h.
  all:swap 1 2.
  (* we go on by specializing H with this new goal *)
  specialize (H h).

  (* let us make the premise p an evar and specialize H with it. *)
  evar (p:nat).
  specialize (H p);subst p.
  (* Let us make another goal for (?p > 0) *)
  assert (?p>0) as h'.
  all:swap 1 2.
  (* we go on by specializing H with this new goal *)
  specialize (H h').
  (* Now we have finished, we finish refining the unknown goal with H itself. *)
  exact H.
  (* Now we are left with 2 subgoals and the initial goal where H has
     been specialized. *)
Abort.


Local Ltac2 Type directarg := [ Quantif | QuantifIgnore | SubGoal | Evar(ident) ].
Local Ltac2 Type namearg := [
    SubGoalAtName(ident) (* make a subgoal with named arg *)                   
  | EvarAtName(ident,ident) (* make an evar with the named arg. *)
].
Local Ltac2 Type numarg := [
  | SubGoalAtNum(int) (* make a subgoal with arg's number *)
  | SubGoalUntilNum(int) (* make subgoals with all non dep hyp until nth one. *)
  | SubGoalAtAll (* make subgoals with all non dep hyp. *)
  ].


Local Ltac2 pr_numarg () a :=
  match a with
  | SubGoalAtNum(i) => fprintf "SubGoalAtNum(%i)" i
  | SubGoalUntilNum(i) => fprintf "SubGoalUntilNum(%i)" i
  | SubGoalAtAll => fprintf "SubGoalAtAll"
  end.

Local Ltac2 pr_directarg () a :=
  match a with
  | Quantif => fprintf "Quantif"
  | QuantifIgnore => fprintf "QuantifIgnore"
  | SubGoal => fprintf "SubGoal"
  | Evar(id) => fprintf "Evar(%I)" id
  end.

Local Ltac2 pr_namearg () a :=
  match a with
  | SubGoalAtName id => fprintf "SubGoalAtName(%I)" id
  | EvarAtName id1 id2 => fprintf "EvarAtName(%I,%I)" id1 id2
  end.
(*
Goal True.
  ltac2:(printf "%a" pr_namearg (SubGoalAtName @toto)).
  ltac2:(printf "%a" (pr_list pr_namearg) ([SubGoalAtName @toto; EvarAtName @titi1 @titi2])).
*)



Local Ltac2 backtrack (msg:string) := Control.zero (Tactic_failure (Some (fprintf "Backtrack: %s" msg))).
Local Ltac2 invalid_arg (msg:string) := Control.throw (Invalid_argument (Some (Message.of_string msg))).

Local Ltac2 mk_evar ename typ :=
  let tac := ltac1:(ename typ|- evar (ename:typ)) in
  tac (Ltac1.of_ident ename) (Ltac1.of_constr typ).
                     
Local Ltac2 assert_evar nme :=
  let tac := ltac1:(nme |-let ev1 := open_constr:(_) in assert ev1 as nme) in
  tac (Ltac1.of_ident nme).
                     

Local Ltac2 intro_typed (name:ident) (typ:constr) :=
  let tac := ltac1:(name typ |- refine (fun (name:typ) => _)) in
  tac (Ltac1.of_ident name) (Ltac1.of_constr typ).

Local Ltac2 specialize_id_id (h:ident) (arg:ident) : unit :=
  let newhyp := Control.hyp arg in
  let hc:constr := Control.hyp h in
  let special := Unsafe.make (Unsafe.App hc [|newhyp|]) in
  Std.specialize (special , Std.NoBindings) None.
  
Local Ltac2 specialize_id_cstr (h:ident) (c:constr) : unit :=
  let hc:constr := Control.hyp h in
  let special := Unsafe.make (Unsafe.App hc [|c|]) in
  Std.specialize (special , Std.NoBindings) None.
  

(* Local Ltac2 pr_debug (h:ident) (ldirectarg:directarg list) (lnameargs:namearg list) *)
(*   (lnumargs:numarg list) (n:int) := *)
(*   let hc := Control.hyp h in *)
(*   let th := Constr.type hc in *)
(*   LibHyps.LibHypsDebug.msgs "--------------"; *)
(*   (* LibHyps.dev.LibHypsDebug.pr_goal(); *) *)
(*   printf "<infomsg>n = %i ; th = %t</infomsg>" n th; *)
(*   printf "<infomsg>lnumargs   = %a</infomsg>" (pr_list pr_numarg) lnumargs; *)
(*   printf "<infomsg>lnameargs  = %a</infomsg>" (pr_list pr_namearg) lnameargs; *)
(*   printf "<infomsg>ldirectarg = %a</infomsg>" (pr_list pr_directarg) ldirectarg. *)


Local Ltac2 rec refine_hd (h:ident) (ldirectarg:directarg list) (lnameargs:namearg list)
  (lnumargs:numarg list) (n:int) :=
  (* pr_debug h ldirectarg lnameargs lnumargs n; *)
  let hc := Control.hyp h in
  let th := Constr.type hc in
  let newn := if is_dep_prod th then n else (Int.add n 1) in
  (* msgc th; *)
  match Unsafe.kind th with
  | Prod _ _ =>
          match ldirectarg with
          | directarg::ldirectarg' =>
              match Unsafe.kind th with
              | Prod bnd _ =>
                  let h_premis := Constr.Binder.name bnd in
                  let typ_premis := Constr.Binder.type bnd in
                  let intronme:ident :=
                    match h_premis with
                      None => Option.get (Ident.of_string "h_premis")
                    | Some idh => idh
                    end in
                  match directarg with
                  | Quantif =>
                      intro_typed intronme typ_premis;
                      specialize_id_id h intronme;
                      refine_hd h ldirectarg' lnameargs lnumargs newn
                  | QuantifIgnore =>
                      intro_typed intronme typ_premis;
                      specialize_id_id h intronme;
                      clear $intronme;
                      refine_hd h ldirectarg' lnameargs lnumargs newn
                  | Evar ename =>
                      let ename := Fresh.in_goal ename in
                      mk_evar ename typ_premis;
                      (* let tac := ltac1:(ename typ_premis|- evar (ename:typ_premis)) in *)
                      (* tac (Ltac1.of_ident ename) (Ltac1.of_constr typ_premis) ; *)
                      specialize_id_id h ename;
                      subst $ename;
                      refine_hd h ldirectarg' lnameargs lnumargs newn
                  | SubGoal =>
                      let gl := Fresh.in_goal @h in (* this uses base name "h" *)
                      (unshelve (epose (_:$typ_premis) as $gl)) >
                        [  | 
                          let special := Control.hyp gl in
                          specialize_id_cstr h special;
                          refine_hd h ldirectarg' lnameargs lnumargs newn ]
                  end
              | _ => invalid_arg "Not a product (directarg)"
              end
          | _ =>
              (* If this succeeds, never go back here from later backtrack. *)
              Control.once
                (fun () => Control.plus
                   (fun() => refine_hd_name h lnameargs lnumargs n)
                   (fun _ => 
                      (* msgs "Backtracking from refine_hd_name "; *)
                      Control.plus
                        (fun () => refine_hd_num h lnameargs lnumargs n)
                        (fun _ =>
                           (*msgs "Backtracking from refine_hd_num "; *)
                           refine_hd h [Quantif] lnameargs lnumargs n)))
                
          end
  | _ => (*base case *)
      match ldirectarg,lnameargs,lnumargs with
      | [],[],[] => exact $hc
      | [],[],[SubGoalAtAll] => exact $hc
      | _ => invalid_arg "Not a product (others)"
      end
        (* (refine_hd_num (h:ident) (ldirectarg:directarg list) (lnameargs:namearg list) *)
           (* (lnumargs:numarg list) (n:int)) *)
  end
    with refine_hd_name (h:ident) (lnameargs:namearg list)
         (lnumargs:numarg list) (n:int) :=
    let hc:constr := Control.hyp h in (* h as a constr *)
    let th:constr := Constr.type hc in (* type of h as a constr *)
    match lnameargs with
    | namearg :: lnameargs' => 
        match Unsafe.kind th with
        | Prod bnd _ =>
            let h_premis := Constr.Binder.name bnd in
            match namearg with
            | SubGoalAtName nme =>
                if map_default (Ident.equal nme) false h_premis
                then refine_hd h [SubGoal] lnameargs' lnumargs n
                else backtrack "refine_hd_name: SubGoalAtName"
            | EvarAtName nme nameevar =>
                if map_default (Ident.equal nme) false h_premis
                then refine_hd h [Evar nameevar] lnameargs' lnumargs n
                else backtrack "refine_hd_name: EvarAtName"
            end
        | _ => invalid_arg "Not a  product (refine_hd_name)"
        end
    | _ => backtrack "refine_hd_name: no namearg"
    end
  with refine_hd_num (h:ident) (lnameargs:namearg list)
       (lnumargs:numarg list) (n:int) :=
    let hc:constr := Control.hyp h in (* h as a constr *)
    let th:constr := Constr.type hc in (* type of h as a constr *)
    let newn := if is_dep_prod th then n else (Int.add n 1) in
    match lnumargs with
    | numarg::lnumargs' =>
        match Unsafe.kind th with
        | Prod _ _ =>
            match numarg with
            | SubGoalAtNum num =>
                if is_dep_prod th
                then backtrack "refine_hd_num: SubGoalAtNum, dep"
                else if Int.le newn num
                     then if Int.equal newn num
                          then refine_hd h [SubGoal] lnameargs lnumargs' n
                          else backtrack "refine_hd_num: SubGoalAtNum,nodep"
                     else invalid_arg "Did you not order the evar numbers?"
            | SubGoalUntilNum num =>
                if is_dep_prod th
                then backtrack "refine_hd_num: SubGoalUntilNum, dep"
                else
                  if Int.equal newn num
                  then refine_hd h [SubGoal] lnameargs lnumargs' n
                  else refine_hd h [SubGoal] lnameargs lnumargs n

            | SubGoalAtAll =>
                if is_dep_prod th
                then backtrack "refine_hd_num: SubGoalAtAll, dep"
                else refine_hd h [SubGoal] lnameargs lnumargs n
            end
        | _ => invalid_arg "Not a product (refine_hd_num)."
        end
     | _ => backtrack "refine_hd_num: no numarg"
    end.

(* initialize n to zero. *)
Local Ltac2 refine_spec h lnameargs lnumargs := refine_hd h [] lnameargs lnumargs 0.

(*
(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Axiom ex_hyp : (forall (b:bool), forall x: nat, eq_one 1 -> forall y:nat, eq_one 2 ->eq_one 3 ->eq_one 4 ->eq_one x ->eq_one 6 ->eq_one y -> eq_one 8 -> eq_one 9 -> False).

Lemma test_esepec: True.
Proof.
  (* specialize ex_hyp as h. *)
  (* especialize ex_hyp at 2 as h. *)
  specialize ex_hyp as H.

  ltac2:(assert_evar @hhh).

  let ev1 := open_constr:(_) in
  assert ev1 as hhh;[
      ltac2:(refine_spec
               (Option.get (Ident.of_string "H"))
               [EvarAtName @b @b; EvarAtName @x @x; EvarAtName @y @y]
               [SubGoalAtNum 3])
    | ];
  [ | match type of hhh with eq_one 1 -> eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end]. 
  [ ..  | match type of hhh with eq_one 1 -> eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].


especialize ex_hyp at 3 with b,x,y as h;
  Undo.


Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 

  let ev1 := open_constr:(_) in
  assert ev1.


  ltac2:(refine_spec
           (Option.get (Ident.of_string "H"))
           [EvarAtName @m @m]
           [SubGoalAtAll]).
  Undo 1.

  (ltac2:(refine_hd
            (Option.get (Ident.of_string "H"))
            []
            [EvarAtName @m @m]
            [SubGoalUntilNum 3]
            0)).
  Undo 1.

  (ltac2:(refine_hd 
            (Option.get (Ident.of_string "H"))
            [Evar @ev]
            [EvarAtName @p @p ;SubGoalAtName @iii]
            [SubGoalAtNum 4]
            0)).

*)

Local Ltac2 cmp_numarg a b :=
  match a with
    SubGoalAtNum na => 
      match b with
        SubGoalAtNum nb => Int.compare na nb
      | _ => -1
      end
  | _ => -1
  end.

Local Ltac2 sort_numargs (l: numarg list): numarg list:= List.sort cmp_numarg l.



(* TODO:sort the names or work modulo order on names? Or simply avoid infinite loops.
   TODO: if there is only one "at" and no "with"
 nor "until", then allow for the subgoal to be kept like an assert. *)
(* builds the inital unknown goal, call the refining tactic, end up by
   replacing h or naming the new hyp. *)
(* Precondition: name is already fresh *)

From Stdlib Require Sorting.Mergesort Structures.OrdersEx.


Local Ltac2 dest_var (c:constr) : ident :=
  match Unsafe.kind c with
  | Unsafe.Var x => x
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "dest_var")))
  end.

Local Ltac2 espec_gen (h:constr) lnames lnums name (replaceb:bool) :=
  let lnums := sort_numargs lnums in
  if is_var h
  then
    let h := dest_var h in
    match replaceb with
      true =>
        assert_evar name > [ (refine_spec h lnames lnums)
                             | Std.clear [h]; Std.rename [(name, h)] ]
    | false =>
        assert_evar name > [ (refine_spec h lnames lnums) | ]
    end
  else 
    (* replaceb should be false in this case. *)
    (let h' := Fresh.in_goal @H in
     Std.specialize (h , Std.NoBindings) (Some (Std.IntroNaming (Std.IntroIdentifier h')));
     assert_evar name > [ (refine_spec h' lnames lnums) | Std.clear [h'] ]).



(*
(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 

  ltac2:(espec_gen constr:(H) [EvarAtName @m @m] [SubGoalAtAll] @toto false).
  Undo 1.
  ltac2:(espec_gen constr:(H) [EvarAtName @m @m] [SubGoalAtAll] @toto true).
  Undo 1.
  ltac2:(espec_gen constr:(H) [EvarAtName @m @m] [SubGoalUntilNum 3] @toto false).
  Undo 1.
  ltac2:(espec_gen constr:(H) [EvarAtName @m @m] [SubGoalUntilNum 3] @toto true).
  Undo 1.
  ltac2:(espec_gen constr:(H) [EvarAtName @m @m] [SubGoalAtAll] @toto false).
  Undo 1.
  ltac2:(espec_gen constr:(H) [EvarAtName @n @n; EvarAtName @m @m] [SubGoalAtNum 4] @toto false).
  Undo 1.
  ltac2:(espec_gen constr:(H) [EvarAtName @n @n; EvarAtName @m @m] [SubGoalAtNum 4] @toto true).
  Undo 1.
*)

Local Ltac2 sgatnum_from_lint (li:int list): numarg list :=
  List.map (fun i => SubGoalAtNum i) li.

Local Ltac2 evatname_from_lid (li:ident list): namearg list :=
  List.map (fun i => EvarAtName i i) li.

(* FIXME li should really be a single int *)
Local Ltac2 sguntilnum_from_lid (li:int list): numarg list :=
  List.map (fun i => SubGoalUntilNum i) li.

Local Ltac2 espec_at_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident) (replaceb:bool):unit :=
  if Bool.and (Bool.neg (is_var h)) replaceb
  then Control.zero (Tactic_failure (Some (fprintf "You must provide a name with 'as'.")))
  else espec_gen h (evatname_from_lid occsevar) (sgatnum_from_lint li) newH replaceb.

Local Ltac2 espec_until_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident) (replaceb:bool) (atAll:bool):unit :=
  (* FIXME: we should also refuse when a section variables is given. *)
  if Bool.and (Bool.neg (is_var h)) replaceb
  then
    Control.zero (Tactic_failure (Some (fprintf "You must provide a name with 'as'.")))
  else
    let c1 := if atAll then [SubGoalAtAll] else sguntilnum_from_lid li in
    espec_gen h (evatname_from_lid occsevar) c1 newH replaceb.


(*
(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Axiom ex_hyp : (forall (b:bool), forall x: nat, eq_one 1 -> forall y:nat, eq_one 2 ->eq_one 3 ->eq_one 4 ->eq_one x ->eq_one 6 ->eq_one y -> eq_one 8 -> eq_one 9 -> False).


Lemma test_espec_namings: forall n:nat, (eq_one n -> eq_one 1 -> False) -> True.
Proof.
  intros n h_eqone.
  specialize min_l as hhh.
  ltac2:(espec_at_using_ltac1_gen constr:(hhh) [1] [@n; @m] @hhh' false).

  let tac := ltac2:(hhh |- call_specialize_ltac2_gen hhh [1] [@n; @m] hhh' false) in
  tac hhh.
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let newH := gen_hyp_name hhh in
  tac hhh  li levars ident:(newH).

  especialize hhh with n,m at 1 as ?.
  especialize min_l with n,m at 1 as ?.


Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 

  ltac2:(espec_at_using_ltac1_gen constr:(H) [2;4] [@m; @p] @toto false).
  Undo 1.
  ltac2:(espec_at_using_ltac1_gen constr:(H) [2;4] [@m; @p] @toto true).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [] [@m]  @toto false true).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [] [@m]  @toto true true).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [3] [@m] @toto false false).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [3] [@m] @toto true false).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [4] [@n ; @m] @toto false false).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [4] [@n ; @m] @toto true false).
  Undo 1.
*)

Local Ltac2 interp_ltac1_id_list (lid:Ltac1.t) : ident list :=
  List.map (fun x => Option.get (Ltac1.to_ident x)) (Option.get (Ltac1.to_list lid)).

Local Ltac2 interp_ltac1_int_list (li:Ltac1.t) : int list :=
  List.map (fun x => Option.get (Ltac1.to_int x)) (Option.get (Ltac1.to_list li)).

Local Ltac2 interp_ltac1_hyp (h:Ltac1.t) : constr := Option.get (Ltac1.to_constr h).

(* call Ltac2'especialize on argscoming from Ltac1 notation *)
Local Ltac2 call_specialize_ltac2_gen (h:Ltac1.t) (li:Ltac1.t) levars newh (replaceb:bool) :=
  let li2 := match Ltac1.to_list li with
              None => []
            | Some _ => interp_ltac1_int_list li
            end in
  let levar2 := match Ltac1.to_list levars with
               None => []
             | Some _ => interp_ltac1_id_list levars
             end in
    espec_at_using_ltac1_gen
      (interp_ltac1_hyp h)
      li2
      levar2
      (Option.get (Ltac1.to_ident newh))
      replaceb.

(* call Ltac2'especialize on argscoming from Ltac1 notation *)

Local Ltac2 call_specialize_until_ltac2_gen (h:Ltac1.t) li levars newh replaceb (atAll:bool) :=
  let li2 := match Ltac1.to_list li with
               None => []
             | Some _ => interp_ltac1_int_list li
             end in
  let levar2 := match Ltac1.to_list levars with
                  None => []
                | Some _ => interp_ltac1_id_list levars
                end in
  if Int.gt (List.length li2) 1
  then
    (* msgi (List.length li'); *)
    Control.zero (Tactic_failure (Some (fprintf "In 'specialize X until I', I must be a singleton.")))
  else 
    espec_until_using_ltac1_gen (interp_ltac1_hyp h) li2 levar2
         (Option.get (Ltac1.to_ident newh)) replaceb atAll.


Ltac gen_hyp_name h := match goal with
                       | |- _ => let _ := is_var h in fresh h "_spec_"
                       | |- _ => fresh "H_spec_"
                       end.
Ltac dummy_term := constr:(Prop).

(* ESPECIALIZE AT *)
(* ********************* *)

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "at" ne_integer_list_sep(li,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.


Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "at" ne_integer_list_sep(li,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let newH := gen_hyp_name h in
  tac h li levars ident:(newH).

Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let newH := gen_hyp_name h in
  tac h li levars ident:(newH).

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "at" ne_integer_list_sep(li,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

(* ********************* *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let li := dummy_term in       (* something that is not a list. *)
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let li := dummy_term in       (* something that is not a list. *)
  let newH := gen_hyp_name h in
  tac h li levars ident:(newH).

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "as" ident(newH) :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
    let levars := dummy_term in       (* something that is not a list. *)
    tac h li levars newH.

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "as" "?" :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
    let levars := dummy_term in       (* something that is not a list. *)
    let newH := gen_hyp_name h in
    tac h li levars ident:(newH).

(* ********************* *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let li := dummy_term  in       (* something that is not a list. *)
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    tac h li levars ident:(dummy_id).




(* ESPECIALIZE UNTIL *)
(* ********************* *)
(* at * is actually a special case of until *)
Tactic Notation "especialize" constr(h) "at" "*" "with"  ne_ident_list_sep(levars,",") :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true true) in
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "with"  ne_ident_list_sep(levars,",") "at" "*" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true true) in
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "at" "*" "with"  ne_ident_list_sep(levars,",") "as" ident(newH)
  :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let li := dummy_term in
    tac h li levars newH.

Tactic Notation "especialize" constr(h) "with"  ne_ident_list_sep(levars,",") "at" "*" "as" ident(newH) :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let li := dummy_term in
    tac h li levars newH.


Tactic Notation "especialize" constr(h) "with"  ne_ident_list_sep(levars,",") "at" "*" "as" "?" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "at" "*" "as" ident(newH) :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars newH.

Tactic Notation "especialize" constr(h) "at" "*" "as" "?" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "at" "*" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).


Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  tac h li levars newH.

(* Strangely putting "with" before "until" is not recognized at
   parsing. Probably because "until" is not a keyword.
   Error: Syntax error: [ltac_use_default] expected after [tactic] (in
   [tactic_command]). *)
 Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "until" ne_integer_list_sep(li,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  tac h li levars newH.

 Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "until" ne_integer_list_sep(li,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).


(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "until" ne_integer_list_sep(li,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "as"  ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let levars := dummy_term in
  tac h li levars ident:(newH).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "as"  "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let nme := gen_hyp_name h in
  let levars := dummy_term in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true false) in
  let nme := gen_hyp_name h in
  let levars := dummy_term in
  tac h li levars ident:(nme).

(*
(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.


Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 

  especialize H with m,p at 2,4 as toto.

  ltac2:(espec_at_using_ltac1_gen constr:(H) [2;4] [@m; @p] @toto false).
  Undo 1.
  ltac2:(espec_at_using_ltac1_gen constr:(H) [2;4] [@m; @p] @toto true).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [] [@m]  @toto false true).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [] [@m]  @toto true true).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [3] [@m] @toto false false).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [3] [@m] @toto true false).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [4] [@n ; @m] @toto false false).
  Undo 1.
  ltac2:(espec_until_using_ltac1_gen constr:(H) [4] [@n ; @m] @toto true false).
  Undo 1.


*)

(* Experimenting a small set of tactic to manipulate a hyp: *)
(*
Ltac quantify H :=
  match type of H with
    (forall x:?t, _) => refine (fun (x:t) => _); specialize (H x)
  end.

Ltac evary H :=
  match type of H with
    (forall x:?t, _) => evar (x:t); specialize (H x);subst x
  end.

Ltac goaly H :=
  match type of H with
    (forall x:?t, _) => [> assert (x:t); [ | specialize (H x)]]
  end.
  
Ltac stopy H := exact H.
Ltac start name :=
  let ev1 := open_constr:(_) in
  assert ev1 as name.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m), p > 0 -> p+m=n) -> False.
Proof.
  intros x y H. 
  start newH.
  quantify H.
  quantify H.
  quantify H.
  quantify H.
  goaly H.
  { now apply PeanoNat.Nat.lt_le_incl. }
  stopy H.
Abort.
*)  


(*
(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Lemma foo: forall x y n m p :nat,
    (forall  (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y n m p H. 
  especialize H at *;[ | | | | | ].
  5: match goal with
       H1 : n < m
         , H2 : n <= m
           , H3 : p > 0
             , H4 : p > 2 |- _ => idtac
     end.
Abort.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 
Abort.


Axiom ex_hyp : (forall (b:bool), forall x: nat, eq_one 1 -> forall y:nat, eq_one 2 ->eq_one 3 ->eq_one 4 ->eq_one x ->eq_one 6 ->eq_one y -> eq_one 8 -> eq_one 9 -> False).

Lemma test_esepec: True.
Proof.
  (* specialize ex_hyp as h. *)
  (* especialize ex_hyp at 2 as h. *)

  especialize ex_hyp at 3 with b,x,y as h;[ ..  | match type of h with eq_one 1 -> eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac end].
  Undo.
Abort.

Lemma test_espec_namings: forall n:nat, (eq_one n -> eq_one 1 -> False) -> True.
Proof.
  intros n h_eqone.
  especialize min_l with n,m at 1 as ?.
  (* especialize PeanOant.Nat.quadmul_le_squareadd with a at 1 as hh : h. *)
  especialize PeanoNat.Nat.quadmul_le_squareadd with a at 1 as hh.
  { apply le_n. }
  specialize min_l as hhh.
  especialize hhh with n,m at 1 as ?.
  especialize min_l with n,m at 1 as ?.
  { apply (le_n O). }
  especialize h_eqone at 2 as h1.
  { reflexivity. }
  unfold eq_one in min_l_spec_.
  (* match type of h2 with 1 = 1 => idtac | _ => fail end. *)
  match type of h1 with eq_one n -> False => idtac | _ => fail end.
  exact I.
Qed.




*)
