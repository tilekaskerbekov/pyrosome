Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils EGraph.Defs Monad.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Lang.SimpleVSubst Lang.SimpleVSTLC Tools.EGraph.Defs
  Tools.EGraph.Automation Tools.EGraph.Test.
Require Import Utils.EGraph.Semantics.
Import PArith.
Import Ascii.AsciiSyntax.
Import StringInstantiation.
Import StateMonad.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Init.Nat.

Definition nat_to_string (n : nat) : string :=
  NilZero.string_of_uint (Nat.to_uint n).

Fixpoint Zip_two_lists (X: Type) (Y: Type) (l1: list X) (l2: list Y) : list (X * Y) :=
  match l1 with
  | nil => nil
  | cons head1 tail1 =>
    match l2 with
    | nil => nil
    | cons head2 tail2 => cons (head1, head2) (Zip_two_lists tail1 tail2)
    end
  end.
Fixpoint Find_x (Y: Type) (key: string) (l: list (string * Y)) : option Y :=
  match l with
  | nil => None
  | cons (head_x, head_y) tail => if (String.eqb key head_x) then (Some head_y) else (Find_x key tail)
  end.
Fixpoint map_indexed (X: Type) (Y: Type) (f : nat -> X -> Y) (L: list X) (start: nat)  : list Y :=
  (* Takes a list X and for each element v at index i replaces it with f (start + i) x and returns a list of such elements of type list Y*)
  match L with
  | nil => nil
  | cons head tail => cons (f start head) (map_indexed f tail (start + 1) )
  end.

(* ------BUILDING_TERMS_and_SORTS_WITH_HOLES---------*)
Local Open Scope string_scope.
Fixpoint insert_terms_into_context
      (list_of_subterms: list term) (explicit_args: list string) (context: ctx) (prefix: string) : list term :=
  match context with
  | nil => nil
  | cons (head_name, head_sort) rest_context =>
    match (Find_x head_name (Zip_two_lists explicit_args list_of_subterms)) with
    | None => (cons (con ("?" ++ prefix ++ head_name) []) (insert_terms_into_context list_of_subterms explicit_args rest_context prefix))
    | Some t => (cons t (insert_terms_into_context list_of_subterms explicit_args rest_context prefix))
    end
  end.
Fixpoint build_term_with_holes_given_prefix (L: lang) (prefix: string) (index: nat) (t: term): term :=
  match t with
  | var _ => t
  | con name_of_rule list_of_subterms =>
      match NamedList.named_list_lookup
        (term_rule [] [] (scon "ty" []))
        L name_of_rule with
          | term_rule context explicit_args some_sort_idk =>
              con name_of_rule
                (insert_terms_into_context
                  ((map_indexed (build_term_with_holes_given_prefix L (prefix ++ (nat_to_string index) ++ "_"))) list_of_subterms 0)
                  explicit_args
                  context
                  (prefix ++ (nat_to_string index) ++ "_"))
          (* The case below never runs *)
          | _ => t
      end
  end.
Definition build_term_with_holes (L: lang) (t: term) :=
  build_term_with_holes_given_prefix L "" 0 t.
Definition build_sort_with_holes_given_prefix (L: lang) (prefix: string) (index: nat) (s: sort): sort :=
  match s with
  | scon name_of_rule list_of_subterms =>
      match NamedList.named_list_lookup
        (sort_rule [] [])
        L name_of_rule with
          | sort_rule context explicit_args =>
              scon name_of_rule
                (insert_terms_into_context
                  ((map_indexed (build_term_with_holes_given_prefix L (prefix ++ (nat_to_string index) ++ "_"))) list_of_subterms 0)
                  explicit_args
                  context
                  (prefix ++ (nat_to_string index) ++ "_"))
          | _ => s
      end
  end.
Definition build_sort_with_holes (L: lang) (s: sort) :=
  build_sort_with_holes_given_prefix L "" 0 s.


Fixpoint get_dummy_names_from_term (t: term) : list string :=
  match t with
  | var _ => []
  | con (String "?" rest) subterms => cons (String "?" rest) (fold_right (@app string) [] (map get_dummy_names_from_term subterms))
  | con _ subterms => (fold_right (@app string) [] (map get_dummy_names_from_term subterms))
  end.

Definition get_dummy_names_from_sort (s: sort) : list string :=
  (* takes a sort with holes *)
  match s with
  | scon (String "?" rest) subterms => cons (String "?" rest) (fold_right (@app string) [] (map get_dummy_names_from_term subterms))
  | scon _ subterms => fold_right (@app string) [] (map get_dummy_names_from_term subterms)
  end.

Fixpoint get_dummy_rules (dummy_names: list string) : lang :=
  match dummy_names with
  | nil => nil
  | cons head rest => cons  (head ++ "_sort", sort_rule [] []) ( cons (head, term_rule [] [] (scon (head ++ "_sort") []))  (get_dummy_rules rest))
  end.
Definition get_dummy_context (dummy_names: list string): ctx :=
  map (fun name => (name, scon "ty" [])) dummy_names.
(* ----------------------------------------*)

Local Open Scope list_scope.
Fixpoint build_ctx_with_holes (L: lang) (context: ctx) :=
  (* takes a pre-elaboration context and a language it type-checks in.
    outputs a context with holes and an extended language with the dummy rule and the additional context rules *)
  match context with
  | nil => (L, nil)
  | (name_n, s) :: rest =>
    let (L', elab_rest) := (build_ctx_with_holes L rest) in
    let sort_with_no_variables := sort_var_to_con s in
    let sort_with_holes := (build_sort_with_holes_given_prefix L' name_n 0 sort_with_no_variables) in
    (
      ((get_dummy_rules (get_dummy_names_from_sort sort_with_holes)) ++ [(name_n, term_rule [] [] sort_with_holes)] ++ L'),
      (name_n , sort_with_holes) :: elab_rest
    )
  end.



(* Injection rules  *)
Fixpoint equalize_terms (L1: list string) (L2: list string) : list (clause string string) :=
  match L1, L2 with
  | _, nil => nil
  | nil, _ => nil
  | head_1 :: rest_1, head_2 :: rest_2 =>
    (eq_clause head_1 head_2) :: equalize_terms rest_1 rest_2
  end.
Local Open Scope string_scope.
Definition injection_rule_from_name_and_rule (name: string) (r: rule) : sequent string string :=
  match r with
  | term_rule context _ _ =>
        let arguments1 := (map (fun x => (fst x) ++ "1") context) in
        let arguments2 := (map (fun x => (fst x) ++ "2") context) in
                {|
              seq_assumptions :=
              [atom_clause
                    {| atom_fn := name ; atom_args := arguments1; atom_ret := "x0" |};
                  atom_clause
                    {| atom_fn := name ; atom_args := arguments2; atom_ret := "x0" |}];
              seq_conclusions := equalize_terms arguments1 arguments2
            |}
  | sort_rule context _ =>
        let arguments1 := (map (fun x => (fst x) ++ "1") context) in
        let arguments2 := (map (fun x => (fst x) ++ "2") context) in
                {|
              seq_assumptions :=
              [atom_clause
                    {| atom_fn := name ; atom_args := arguments1; atom_ret := "x0" |};
                  atom_clause
                    {| atom_fn := name ; atom_args := arguments2; atom_ret := "x0" |}];
              seq_conclusions := equalize_terms arguments1 arguments2
            |}
  (* Case below should never run, but if it runs we return a trivial rule *)
  | _ => {|
              seq_assumptions :=
              [atom_clause
                    {| atom_fn := name ; atom_args := ["X"]; atom_ret := "x" |};
                  atom_clause
                    {| atom_fn := name ; atom_args := ["X"]; atom_ret := "x" |}];
              seq_conclusions := equalize_terms ["X"] ["X"]
            |}
  end.
Definition build_injection_rule (L: lang) (name: string): sequent string string :=
  match Find_x name L with
  | Some r =>
    injection_rule_from_name_and_rule name r
  | None =>
          {|
              seq_assumptions :=
              [atom_clause
                    {| atom_fn := name ; atom_args := ["X"]; atom_ret := "x" |};
                  atom_clause
                    {| atom_fn := name ; atom_args := ["X"]; atom_ret := "x" |}];
              seq_conclusions := equalize_terms ["X"] ["X"]
            |}
  end.
Definition build_injection_rules (names: list string) (L: lang): list (sequent string string) :=
  map (build_injection_rule L) names.
(* ----------------------------- *)

Local Open Scope char_scope.
Definition weight (a: atom string string) : option positive :=
match a with
| Build_atom (String "?" _) [] _ => None
| _ => Some (1 %positive)
end.
Local Open Scope string_scope.
Definition empty_egraph := (Utils.EGraph.Defs.empty_egraph (idx:=string) (default : string)
                              (symbol:=string) (symbol_map := string_trie_map)
                              (idx_map := string_trie_map) (option positive)).
Local Open Scope list_scope.
Fixpoint con_to_var (context: ctx) (t: term) : term :=
  match t with
  | con name [] =>
      if (inb name (map fst context)) then (var name) else t
  | con name subterms => con name (map (con_to_var context) subterms)
  | _ => t
  end.
Definition result_to_term (result: Result.result term) : term :=
  match result with
  | Result.Success t => t
  | _ => default
  end.
Definition result_to_sort (result: Result.result sort) : sort :=
  match result with
  | Result.Success s => s
  | _ => default
  end.
Definition term_to_sort (t: term) : sort :=
  match t with
  | var x => scon x []
  | con n s => scon n s
  end.
Definition state_operation (L: lang) (inj_rules: list string) :=
  @saturate_until string String.eqb string_succ
    (default (A:= string))
    string
    string_trie_map
    string_ptree_map_plus string_trie_map string_ptree_map_plus
    string_list_trie_map (option positive) (weighted_depth_analysis weight) (@PosListMap.compat_intersect)
    100
    (
    @QueryOpt.build_rule_set string String.eqb string_succ (default (A:= string))
      string  string_trie_map string_ptree_map_plus string_trie_map
      string_list_trie_map 100  (build_injection_rules inj_rules L)
    )
    (Mret false) 100
    .

(* Breaking up egraph operations: *)

(* Definition add_elab_term (L: lang) (t: term) (Id: string): state instance string :=  *)

(* INFERENCE: *)
Definition infer_term (L: lang) (inj_rules: list string) (context: ctx) (t: term) (s: sort) :=
  let Language_plus_rules := L ++ (ctx_to_rules context) in
  let term_with_no_variables := (var_to_con t) in
  let term_with_holes := build_term_with_holes Language_plus_rules term_with_no_variables in
  let new_context := context ++ get_dummy_context (get_dummy_names_from_term (term_with_holes)) in
  let dummy_rules := get_dummy_rules (get_dummy_names_from_term (term_with_holes)) in
  let '(str, inst2) := add_open_term weight (Language_plus_rules ++ dummy_rules) true [] term_with_holes empty_egraph in
  let '(id_sort, inst3) := add_open_sort weight (Language_plus_rules ++ dummy_rules) true [] (sort_var_to_con s) inst2 in
  let '(id_original_sort, inst4) := @hash_entry string String.eqb string_succ string string_trie_map string_trie_map string_list_trie_map
                                 _ (weighted_depth_analysis weight) sort_of [str] inst3 in
  let '(_, inst5) := @union string String.eqb (default (A:= string)) string string_trie_map string_trie_map string_list_trie_map
                     _ (weighted_depth_analysis weight) id_sort id_original_sort inst4 in

  let '(_, inst6) := (state_operation L inj_rules) inst5 in
  con_to_var new_context (result_to_term (extract_weighted inst6 1000 str)).

Definition infer_sort (L: lang) (inj_rules: list string) (context: ctx) (s: sort) : sort :=
  let Language_plus_rules := L ++ (ctx_to_rules context) in
  let sort_with_no_variables := (sort_var_to_con s) in
  let sort_with_holes := build_sort_with_holes Language_plus_rules sort_with_no_variables in
  let dummy_rules := get_dummy_rules (get_dummy_names_from_sort (sort_with_holes)) in
  let '(str, inst2) := add_open_sort weight (Language_plus_rules ++ dummy_rules) true [] sort_with_holes empty_egraph in

  let '(_, inst3) := (state_operation L inj_rules) inst2 in
  term_to_sort(result_to_term (extract_weighted inst3 1000 str)).

Fixpoint infer_ctx (L: lang) (inj_rules: list string) (context: ctx) : ctx :=
  match context with
  | nil => nil
  | (n, s) :: rest =>
    let elab_rest := (infer_ctx L inj_rules rest) in
      (n, (infer_sort L inj_rules elab_rest s)) :: elab_rest
  end.

Definition add_ctx_with_holes_to_egraph (L: lang) (context: ctx): (state instance (named_list string)) :=
  (* takes a context holes, a language it type checks in.
      adds the sorts in the context to the egraph. *)
  list_Mmap ( fun '(n, s) => Mbind (fun str => Mret (n, str)) (add_open_sort weight L true [] s) ) context.


Definition infer_rule (L: lang) (inj_rules: list string) (r: rule) :=
  match r with
  | sort_rule c args => sort_rule (infer_ctx L inj_rules c) args
  | term_rule c args t => let ec := infer_ctx L inj_rules c in
                          let et := infer_sort L inj_rules ec t in
                          term_rule ec args et
  | sort_eq_rule c t1 t2 => let ec := infer_ctx L inj_rules c in
                            let et1 := infer_sort L inj_rules ec t1 in
                            let et2 := infer_sort L inj_rules ec t2 in
                            sort_eq_rule ec et1 et2
  | term_eq_rule c e1 e2 t => let ec := infer_ctx L inj_rules c in
                              let et := infer_sort L inj_rules ec t in
                              let ee1 := infer_term L inj_rules ec e1 et in
                              let ee2 := infer_term L inj_rules ec e2 et in
                              term_eq_rule ec ee1 ee2 et
  end.

Fixpoint infer_lang (L: lang) (inj_rules: list string) :=
  match L with
  | nil => nil
  | (n, r) :: rest => (n, infer_rule rest inj_rules r) :: (infer_lang rest inj_rules)
  end.
