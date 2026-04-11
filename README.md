This Library provides several coq tactics and tacticals to deal with
hypothesis during a proof.

Main page and documentation: https://github.com/Matafou/LibHyps

Demo file [demo.v](https://github.com/Matafou/LibHyps/blob/master/Demo/demo.v) acts as a documentation.

# Short description:

LibHyps provides utilities for hypothesis manipulations.

- a new tactic `especialize H at ...` to generate one or several
  subgoals from the premiese of `H` (which can be a hypothesis name or
  an lemma name).
- a set of tacticals to apply or iterate tactics either on all
  hypothesis of a goal or on "new' hypothesis after a tactic. It also
  provide syntax for a few predefined such iterators.

# Quick Test
## Quick install using opam

If you have not done it already add the coq platform repository to opam!

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
```

and then:

```bash
opam install coq-libhyps
```

## Quick install using github:

Clone the github repository:

```bash
git clone https://github.com/Matafou/LibHyps
```
then compile:
```bash
configure.sh
make
make install
```

## Quick test:

```coq
Require Import LibHyps.LibHyps.
```

Demo files [demo.v](https://github.com/Matafou/LibHyps/blob/master/Demo/demo.v).



## The especialize tactic

Let `H` be a hypothesis (or lemma) with type `∀ x y z, H1 -> H2 -> H3 -> C`.

+ `especialize H at 2.` Creates a subgoal of the form:

  ```
   ∀ x y z, H1 -> H2
  ```
  
  and specializes `H` with this subgoal:
  
  ```
  H: ∀ x y z, H1 -> H3 -> C
  ```

+ `especialize H at 2,3.` does what you think: two subgoals. Note that
  the order of hyps.

+ `especialize H at * with x,y.` Creates one subgoal for each dependent
    premise of `H`.

+ `especialize H until 2 [as h].` Creates one subgoal for each 2 first
  dependent premises of `H`. 
    
+ By default all non-dependent hypothesis of `H` are left quantified.
  But you can specify the ones that should rather be transformed into
  existential variables. Examples:

  + `especialize H at 2 with y.` Creates an evar `?y` subgoal of the form:

    ```
     ∀ x z, H1 -> H2
    ```
  
    and specializes `H` with this subgoal and evar `?y`:
  
    ```
    H: ∀ x z, H1 -> H3 -> C
    ```
    (where H1 and H3 reference `?y` now).
    
  + Several evars can be specified, they must be in order:

    ```especialize H at 2 with y.```


Note that (contrary to previous versions of this library), if you
forget to list a variable, the tactic won't fail. Instead it will
simply leave the variable quantified in the original hypothesis **and
in subsequently created subgoals**.

For example, after this:

  ``` coq
  Lemma test_espec8: forall x:nat, (forall a :nat, a = 1 -> x = 1 -> False) -> x > 1.
  Proof.
    intros x h. 
  ```

the goal looks like this

``` coq
  x : nat
  h : forall a : nat, a = 1 -> x = 1 -> False
  ============================
  x > 1
```

the following tactic:

``` coq
especialize h with a at 1.
```

gives two subgoals:

``` coq
  x : nat
  ============================
  ?a = 1

  x : nat
  h : x = 1 -> False
  ============================
  x > 1

```

Whereas

``` coq
especialize h at 1.
```

gives (note how `a` is quantified in both subgoals, which makes the
first one unprovable):

``` coq
  x, a : nat
  ============================
  a = 1
  
  x : nat
  h : nat -> x = 1 -> False
  ============================
  x > 1
```


## QUICK REF: Pre-defined tacticals /s /n...

The most useful user-dedicated tacticals are the following

  + `tac /s` try to apply `subst` on each new hyp.
  + `tac /r` revert each new hyp.
  + `tac /n` auto-rename each new hyp.
  + `tac /g` group all non-Prop new hyp at the top of the goal.
  + combine the above, as in `tac /s/n/g`.
  + usual combinations have shortcuts: `\sng`, `\sn`,`\ng`,`\sg`...

# Install


# More information

## Deprecation from 1.0.x to 2.0.x

  + "!tac", "!!tac" etc are now only loaded if you do: `Import
    LibHyps.LegacyNotations.`, the composable tacticals described
    above are preferred.
  + "tac1 ;; tac2" remains, but you can also use "tac1; { tac2 }".
  + "tac1 ;!; tac2" remains, but you can also use "tac1; {< tac2 }".

## KNOWN BUGS

Due to Ltac limitation, it is difficult to define a tactic notation
`tac1 ; { tac2 }` which delays `tac1` and `tac2` in all cases.
Sometimes (rarely) you will have to write `(idtac; tac1); {idtac;
tac2}`. You may then use tactic notation like: `Tactic Notation tac1'
:= idtac; tac1.`.

## Examples

```coq
Require Import LibHyps.LibHyps.

Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2)  -> z = b + x-> True.
Proof.
  intros.
  (* ugly names *)
  Undo.
  (* Example of using the iterator on new hyps: this prints each new hyp name. *)
  intros; {fun h => idtac h}.
  Undo.
  (* This gives sensible names to each new hyp. *)
  intros ; { autorename }.
  Undo.
  (* short syntax: *)
  intros /n.
  Undo.
  (* same thing but use subst if possible, and group non prop hyps to the top. *)
  intros ; { substHyp }; { autorename}; {move_up_types}.
  Undo.
  (* short syntax: *)  
  intros /s/n/g.
  Undo.
  (* Even shorter: *)  
  intros /s/n/g.

  (* Let us instantiate the 2nd premis of h_all_eq_add_add without copying its type: *)
  especialize h_all_eq_add_add_ with u at 2.
  { apply Nat.add_0_l. }
  (* now h_all_eq_add_add is specialized *)
  Undo 6.
  intros until 1.
  (** The taticals apply after any tactic. Notice how H:x=y is not new
    and hence not substituted, whereas z = b + x is. *)
  destruct x eqn:heq;intros /sng.
  - apply I.
  - apply I.
Qed.
```

## Short Documentation

The following explains how it works under the hood, for people willing
to apply more generic iterators to their own tactics. See also the code.
  
### Iterator on all hypothesis

  + `onAllHyps tac` does `tac H` for each hypothesis `H` of the current goal.
  + `onAllHypsRev tac` same as `onAllHyps tac` but in reverse order
    (good for reverting for instance).


### Iterators on ALL NEW hypothesis (since LibHyps-1.2.0)

  + `tac1 ;{! tac2 }` applies `tac1` to current goal and then `tac2`
    to *the list* of all new hypothesis in each subgoal (iteration:
    oldest first).
    The list is a term of type `LibHyps.TacNewHyps.DList`. See the code.
  + `tac1 ;{!< tac2 }` is similar but the list of new hyps is reveresed.

### Iterators on EACH NEW hypothesis

  + `tac1 ;{ tac2 }` applies `tac1` to current goal and then `tac2` to
    each new hypothesis in each subgoal (iteration: older first).
  + `tac1 ;{< tac2 }` is similar but applies tac2 on newer hyps first.

  + `tac1 ;; tac2` is a synonym of `tac1; { tac2 }`.
  + `tac1 ;!; tac2` is a synonym of `tac1; {< tac2 }`.

### Customizable hypothesis auto naming system

Using previous taticals (in particular the `;!;` tactical), some
tactic allow to rename hypothesis automatically.

- `autorename H` rename `H` according to the current naming scheme
  (which is customizable, see below).

- `rename_all_hyps` applies `autorename` to all hypothesis.

- `!tac` applies tactic `tac` and then applies autorename to each new
  hypothesis. Shortcut for: `(Tac ;!; revert_if_norename ;;
  autorename).`.`

- `!!tac` same as `!tac` with lesser priority (less than `;`) to apply
  renaming after a group of chained tactics.

#### How to cstomize the naming scheme

The naming engine analyzes the type of hypothesis and generates a name
mimicking the first levels of term structure. At each level the
customizable tactic `rename_hyp` is called. One can redefine it at
will. It must be of the following form:

```coq
(** Redefining rename_hyp*)
(* First define a naming ltac. It takes the current level n and
   the sub-term th being looked at. It returns a "name". *)
Ltac rename_hyp_default n th :=
   match th with
   | (ind1 _ _) => name (`ind1`)
   | (ind1 _ _ ?x ?y) => name (`ind1` ++ x#(S n)x ++ y$n)
   | f1 _ ?x = ?y => name (`f1` ++ x#n ++ y#n)
   | _ => previously_defined_renaming_tac1 n th (* cumulative with previously defined renaming tactics *)
   | _ => previously_defined_renaming_tac2 n th
   end.

(* Then overwrite the definition of rename_hyp using the ::= operator. :*)
Ltac rename_hyp ::= my_rename_hyp.
```

Where:

- `` `id` `` to use the name id itself
- `t$n` to recursively call the naming engine on term t, n being the maximum depth allowed
- `name ++ name` to concatenate name parts.


#### How to define variants of these tacticals?

Some more example of tacticals performing cleaning and renaming on new
hypothesis.

```coq
(* subst or revert *)
Tactic Notation (at level 4) "??" tactic4(tac1) :=
  (tac1 ;; substHyp ;!; revertHyp).
(* subst or rename or revert *)
Tactic Notation "!!!" tactic3(Tac) := (Tac ;; substHyp ;!; revert_if_norename ;; autorename).
(* subst or rename or revert + move up if in (Set or Type). *)
Tactic Notation (at level 4) "!!!!" tactic4(Tac) :=
      (Tac ;; substHyp ;!; revert_if_norename ;; autorename ;; move_up_types).
```


# About the logical "completeness" of `especialize`

Suppose we have this goal:


```coq
  Lemma foo: (forall x:nat, x = 1 -> (x>0) -> x < 0) -> False.
  Proof.
    intros h.

h : forall x : nat, x = 1 -> x > 0 -> x < 0
  ============================
  False

especialize h with x at 2.


  h : ?x = 1 -> ?x > 0 -> ?x < 0
  ============================
  ?x > 0

goal 2 (ID 88) is:
 False

```

Note that in this case it would be preferable (and logically more
accurate) to have a hypothesis `h2: ?x = 1` in the context, since the
premise 2 of H needs only to be proved when premise 1 is true. Note
however that in this kind of situation most users would wait to be
able to prove premise 1 before instantiating premise 2. `especialize`
does not cover this kind of subtleties. Another tactic is under
development to support this kind of reasoning.



<!--  LocalWords:  subgoal unifiable evars
 -->
