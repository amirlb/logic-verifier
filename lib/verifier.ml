module LogicOp = struct
  type 'a t =
    | And of 'a * 'a
    | Or of 'a * 'a
    | Implies of 'a * 'a
    | Iff of 'a * 'a
    | Not of 'a
  [@@deriving ord, map]

  let to_string = function
    | And(lhs, rhs) -> Printf.sprintf "(%s ∧ %s)" lhs rhs
    | Or(lhs, rhs) -> Printf.sprintf "(%s ∨ %s)" lhs rhs
    | Implies(lhs, rhs) -> Printf.sprintf "(%s ⇒ %s)" lhs rhs
    | Iff(lhs, rhs) -> Printf.sprintf "(%s ⇔ %s)" lhs rhs
    | Not(inner) -> Printf.sprintf "¬%s" inner

  let eval = function
    | And(lhs, rhs) -> lhs && rhs
    | Or(lhs, rhs) -> lhs || rhs
    | Implies(lhs, rhs) -> not lhs || rhs
    | Iff(lhs, rhs) -> lhs = rhs
    | Not(value) -> not value

  let collapse f = function
    | And(lhs, rhs) -> f lhs rhs
    | Or(lhs, rhs) -> f lhs rhs
    | Implies(lhs, rhs) -> f lhs rhs
    | Iff(lhs, rhs) -> f lhs rhs
    | Not(value) -> value

  let map2_unify f c1 c2 = match c1, c2 with
    | And(lhs1, rhs1), And(lhs2, rhs2) -> Some(And(f lhs1 lhs2, f rhs1 rhs2))
    | Or(lhs1, rhs1), Or(lhs2, rhs2) -> Some(Or(f lhs1 lhs2, f rhs1 rhs2))
    | Implies(lhs1, rhs1), Implies(lhs2, rhs2) -> Some(Implies(f lhs1 lhs2, f rhs1 rhs2))
    | Iff(lhs1, rhs1), Iff(lhs2, rhs2) -> Some(Iff(f lhs1 lhs2, f rhs1 rhs2))
    | Not(inner1), Not(inner2) -> Some(Not(f inner1 inner2))
    | _ -> None
end

module IntMap = Map.Make(Int)

module Pattern = struct
  type t =
    | MetaVar of int
    | Op of t LogicOp.t
  [@@deriving ord]

  type inference = t list * t

  let rec to_string = function
    | MetaVar i -> Printf.sprintf "%d" i
    | Op expr -> LogicOp.to_string (LogicOp.map to_string expr)

  module IntSet = Set.Make(Int)

  let rec evaluate assignment = function
    | MetaVar i -> assignment i
    | Op expr -> LogicOp.(eval (map (evaluate assignment) expr))

  let rec metavars = function
    | MetaVar i -> IntSet.singleton i
    | Op expr -> LogicOp.(collapse IntSet.union (map metavars expr))

  let all_assignments metavars =
    let metavar_inds = IntMap.of_seq (Seq.mapi (fun i var -> (var, i)) (IntSet.to_seq metavars)) in
    Seq.init
      (1 lsl (IntSet.cardinal metavars))
      (fun i var -> (i lsr (IntMap.find var metavar_inds)) land 1 = 1)

  let disproves (premises, conclusion) assignment =
    List.for_all (evaluate assignment) premises && not (evaluate assignment conclusion)

  let consequence premises conclusion =
    let metavars =
      List.fold_left
        (fun acc pattern -> IntSet.union acc (metavars pattern))
        (metavars conclusion)
        premises in
    if IntSet.cardinal metavars > 20 then failwith "Too complicated, cannot verify";
    let inference = (premises, conclusion) in
    if Seq.exists (disproves inference) (all_assignments metavars) then failwith "Inference is not valid";
    inference
end

module Var1 = struct
  type t = {
    name : string;
    ind : int;
  }

  let equal x y = x.ind = y.ind
  let compare x y = Int.compare x.ind y.ind

  let gen =
    let ctr = ref 0
    in fun name -> ctr := !ctr + 1; { ind = !ctr; name }
end

module Var2 = struct
  type t = {
    arity : int;
    ind : int;
    name : string;
  }

  let equal x y = x.ind = y.ind
  let compare x y = Int.compare x.ind y.ind

  let gen =
    let ctr = ref 0
    in fun arity name -> ctr := !ctr + 1; { arity; ind = !ctr; name }
end

module Var1Set = Set.Make(Var1)
module Var1Map = Map.Make(Var1)
module Var2Set = Set.Make(Var2)

module VarSets = struct
  type t = { vars1 : Var1Set.t ; vars2 : Var2Set.t }

  let union a b = {
    vars1 = Var1Set.union a.vars1 b.vars1;
    vars2 = Var2Set.union a.vars2 b.vars2;
  }

  let mem_var1 var free_vars = Var1Set.mem var free_vars.vars1
  let mem_var2 var free_vars = Var2Set.mem var free_vars.vars2
end

module BaseFormula = struct
  type 'a t =
    | Atom of 'a
    | Op of 'a t LogicOp.t
    | Forall of string * 'a t
    | Exists of string * 'a t
    | Forall2 of int * string * 'a t

  let rec map_aux f depth = function
    | Atom atom -> f depth atom
    | Op expr -> Op (LogicOp.map (map_aux f depth) expr)
    | Forall (name, inner) -> Forall (name, map_aux f (depth + 1) inner)
    | Exists (name, inner) -> Exists (name, map_aux f (depth + 1) inner)
    | Forall2 (arity, name, inner) -> Forall2 (arity, name, map_aux f (depth + 1) inner)

  let general_map f = map_aux f 0

  let map f = general_map (fun depth atom -> Atom (f depth atom))
end

type 'a debruijn = Bound of int | Free of 'a

let equal_debruijn equal x y =
  match x, y with
    | Bound i, Bound j -> i = j
    | Free x, Free y -> equal x y
    | _, _ -> false

module rec Formula : sig
  type atom =
    | Apply of Var2.t debruijn * Var1.t debruijn list
    | Shorthand of Definition.t * Var1.t debruijn list * t Lazy.t

  and t = atom BaseFormula.t
end = Formula
and Definition : sig
  type t = { symbol : Var2.t; body : Template.t }
end = Definition
and Template : sig
  type 'a or_parameter = Param of int | Var of 'a

  type atom =
    | Apply of Var2.t debruijn * Var1.t or_parameter debruijn list
    | Shorthand of Definition.t * Var1.t or_parameter debruijn list

  type t = atom BaseFormula.t
end = Template

let build_template param_inds =
  let transform_var depth = function
    | Bound index -> assert (index <= depth); Bound index
    | Free var -> match Var1Map.find_opt var param_inds with
        | None -> Free (Template.Var var)
        | Some param_ind -> Free (Template.Param param_ind)
  in let validate_pred depth = function
    | Bound index -> assert (index <= depth)
    | _ -> ()
  in let aux depth = function
    | Formula.Apply (pred, args) ->
        validate_pred depth pred;
        Template.Apply (pred, List.map (transform_var depth) args)
    | Formula.Shorthand (defn, args, _) ->
      Template.Shorthand (defn, List.map (transform_var depth) args)
  in BaseFormula.map aux

let template_of_formula arity f =
  let args = List.init arity (fun i -> Var1.gen (Printf.sprintf "x%d" i)) in
  let param_inds = Var1Map.of_list (List.mapi (fun i arg -> (arg, i)) args) in
  build_template param_inds (f args)

let rec apply_template args =
  let transform_var depth = function
    | Bound index -> assert (index <= depth); Bound index
    | Free (Template.Var var) -> Free var
    | Free (Template.Param i) -> match List.nth args i with
        | Bound index -> Bound (depth + index)
        | var -> var
  in let aux depth = function
    | Template.Apply (pred, args) -> Formula.Apply (pred, List.map (transform_var depth) args)
    | Template.Shorthand (defn, args) -> apply_definition defn (List.map (transform_var depth) args)
  in BaseFormula.map aux

and apply_definition defn args =
  assert (defn.symbol.arity = List.length args);
  Formula.Shorthand (defn, args, lazy (apply_template args defn.body))

let map_var1 f =
  let aux depth = function
    | Formula.Apply (pred, args) -> Formula.Apply (pred, List.map (f depth) args)
    (* TODO: don't re-create the thunk if we get the exact same list of vars *)
    | Formula.Shorthand (defn, args, _) -> apply_definition defn (List.map (f depth) args)
  in BaseFormula.map aux

let bind_var1 var =
  let transform_var depth = function
    | Free x when Var1.equal x var -> Bound depth
    | v -> v
  in map_var1 transform_var

let substitute_var1 var =
  let transform_var depth = function
    | Bound index when index = depth -> Free var
    | v -> v
  in map_var1 transform_var

let bind_pred var =
  let aux depth = function
    | Formula.Apply (Free pred, args) when Var2.equal pred var -> Formula.Apply (Bound depth, args)
    | atom -> atom
  in BaseFormula.map aux

let free_vars_of_args args =
  Var1Set.of_list (List.filter_map (function Free var -> Some var | Bound _ -> None) args)

let free_vars_of_atom = function
  | Formula.Apply (pred, args) -> {
        VarSets.vars1 = free_vars_of_args args;
        VarSets.vars2 = match pred with Free var -> Var2Set.singleton var | Bound _ -> Var2Set.empty;
      }
  | Formula.Shorthand (_, args, _) -> {
        VarSets.vars1 = free_vars_of_args args;
        VarSets.vars2 = Var2Set.empty;
      }

let rec free_vars = function
  | BaseFormula.Atom atom -> free_vars_of_atom atom
  | BaseFormula.Op expr -> LogicOp.(collapse VarSets.union (map free_vars expr))
  | BaseFormula.Forall (_, inner) -> free_vars inner
  | BaseFormula.Exists (_, inner) -> free_vars inner
  | BaseFormula.Forall2 (_, _, inner) -> free_vars inner

let rec equal_formula (formula1 : Formula.t) (formula2 : Formula.t) =
  match (formula1, formula2) with
    | Atom (Shorthand (defn1, args1, thunk1)), Atom (Shorthand (defn2, args2, thunk2)) ->
        if defn1.symbol.ind = defn2.symbol.ind && List.for_all2 (equal_debruijn Var1.equal) args1 args2
          then true
          else equal_formula (Lazy.force thunk1) (Lazy.force thunk2)
    | Atom (Shorthand (_, _, thunk)), _ -> equal_formula (Lazy.force thunk) formula2
    | _, Atom (Shorthand (_, _, thunk)) -> equal_formula formula1 (Lazy.force thunk)
    | Atom (Apply (pred1, args1)), Atom (Apply (pred2, args2)) ->
        (equal_debruijn Var2.equal) pred1 pred2 && List.for_all2 (equal_debruijn Var1.equal) args1 args2
    | Op expr, Op expr2 -> (
          match LogicOp.map2_unify equal_formula expr expr2 with
            | Some outcomes -> LogicOp.collapse (&&) outcomes
            | None -> false
        )
    | Forall (_, formula1), Forall (_, formula2) -> equal_formula formula1 formula2
    | Exists (_, formula1), Exists (_, formula2) -> equal_formula formula1 formula2
    | Forall2 (_, _, formula1), Forall2 (_, _, formula2) -> equal_formula formula1 formula2
    | _ -> false

(* TODO: handle name collisions *)
let rec to_string_aux names : Formula.t -> string = function
  | Atom (Apply (pred, args)) ->
      Printf.sprintf "%s(%s)"
        (match pred with Free var -> var.name | Bound index -> List.nth names index)
        (String.concat ", " (List.map (function Free var -> var.Var1.name | Bound index -> List.nth names index) args))
  | Atom (Shorthand (_, _, _)) -> "TODO"
  | Op expr -> LogicOp.to_string (LogicOp.map (to_string_aux names) expr)
  | Forall (name, inner) -> Printf.sprintf "∀%s %s" name (to_string_aux (name :: names) inner)
  | Exists (name, inner) -> Printf.sprintf "∃%s %s" name (to_string_aux (name :: names) inner)
  | Forall2 (arity, name, inner) -> Printf.sprintf "∀%s/%d %s" name arity (to_string_aux (name :: names) inner)
let string_of_formula = to_string_aux []

module Context = struct
  type t = (Formula.t * VarSets.t) list

  let singleton formula = [(formula, free_vars formula)]

  let rec add formula = function
    | [] -> singleton formula
    | (formula', _) :: context ->
        if equal_formula formula formula'
          then context
          else add formula context

  let remove formula =
    List.filter (fun (formula', _) -> not (equal_formula formula formula'))

  let has_free_var1 var =
    List.exists (fun (_, free_vars) -> VarSets.mem_var1 var free_vars)

  let has_free_var2 var =
    List.exists (fun (_, free_vars) -> VarSets.mem_var2 var free_vars)

  let union =
    List.fold_left (fun ctx (formula, _) -> add formula ctx)

  let union_all =
    List.fold_left union []
end

module Judgement = struct
  type t = Context.t * Formula.t

  let to_string (context, conclusion) =
    Printf.sprintf "%s ⊢ %s"
      (String.concat ", " (List.map (fun (premise, _) -> string_of_formula premise) context))
      (string_of_formula conclusion)
end

(* Public interface follows *)

type pattern = Pattern.t
type inference = Pattern.inference

let metavar n = Pattern.MetaVar n
let pattern_and lhs rhs = Pattern.(Op (And (lhs, rhs)))
let pattern_or lhs rhs = Pattern.(Op (Or (lhs, rhs)))
let pattern_implies lhs rhs = Pattern.(Op (Implies (lhs, rhs)))
let pattern_iff lhs rhs = Pattern.(Op (Iff (lhs, rhs)))
let pattern_not inner = Pattern.(Op (Not inner))

let consequence = Pattern.consequence
let string_of_pattern = Pattern.to_string

type variable = Var1.t
type predicate =
  | Auto of Var2.t
  | Builtin of Var2.t
  | Template of int * Template.t
  | Definition of Definition.t
type formula = Formula.t
type judgement = Judgement.t

let make_builtin ~arity ~name = Builtin (Var2.gen arity name)

let template_of_var2 var =
  (
    var.Var2.arity,
    BaseFormula.Atom (Template.Apply (Free var, List.init var.arity (fun i -> Free (Template.Param i))))
  )

let as_template = function
  | Auto _ -> failwith "Cannot make a definition from a temporary variable"
  | Builtin var -> template_of_var2 var
  | Template (arity, template) -> (arity, template)
  | Definition defn -> template_of_var2 defn.symbol

let make_definition pred ~name =
  let (arity, template) = as_template pred in
  Definition { symbol = Var2.gen arity name; body = template }

let predicate_of_formula ~arity f =
  let template = template_of_formula arity f in
  Template (arity, template)

let string_of_predicate _ = failwith "TODO"

let arity_of_predicate = function
  | Auto var -> var.arity
  | Builtin var -> var.arity
  | Template (arity, _) -> arity
  | Definition defn -> defn.symbol.arity

let apply_predicate pred args =
  assert (arity_of_predicate pred = List.length args);
  match pred with
    | Auto var -> BaseFormula.Atom (Formula.Apply (Free var, args))
    | Builtin var -> BaseFormula.Atom (Formula.Apply (Free var, args))
    | Template (_, template) -> apply_template args template
    | Definition defn -> BaseFormula.Atom (Formula.Apply (Free defn.symbol, args))

let apply pred args =
  apply_predicate pred (List.map (fun var -> Free var) args)

let and_ lhs rhs = BaseFormula.(Op (And (lhs, rhs)))
let or_ lhs rhs = BaseFormula.(Op (Or (lhs, rhs)))
let implies lhs rhs = BaseFormula.(Op (Implies (lhs, rhs)))
let iff lhs rhs = BaseFormula.(Op (Iff (lhs, rhs)))
let not_ inner = BaseFormula.(Op (Not inner))

let forall ~name f = let x = Var1.gen name in BaseFormula.Forall (name, bind_var1 x (f x))
let exists ~name f = let x = Var1.gen name in BaseFormula.Exists (name, bind_var1 x (f x))
let forall2 ~arity ~name f = let p = Var2.gen arity name in BaseFormula.Forall2 (arity, name, bind_pred p (f (Auto p)))

let judgement_premises (context, _) =
  Seq.map (fun (premise, _) -> premise) (List.to_seq context)

let judgement_conclusion (_, concolusion) = concolusion

let string_of_judgement = Judgement.to_string

let assume formula =
  (Context.singleton formula, formula)

let assuming assumption derivation =
  let (context, conclusion) = derivation (assume assumption) in
  (
    Context.remove assumption context,
    implies assumption conclusion
  )

let kleisli f g x = Option.bind (f x) g

let rec unify pattern (formula : formula) assignment =
  match pattern, formula with
    | Pattern.MetaVar i, _ ->
        (match IntMap.find_opt i assignment with
          | Some formula' -> if equal_formula formula formula' then Some assignment else None
          | None -> Some (IntMap.add i formula assignment))
    | Op(pexpr), Op(fexpr) ->
        Option.bind
          (LogicOp.map2_unify unify pexpr fexpr)
          (fun expr -> LogicOp.collapse kleisli expr assignment)
    | _, Atom (Shorthand (_, _, thunk)) ->
        unify pattern (Lazy.force thunk) assignment
    | _, _ -> None

let matches (inference_premises, inference_conclusion) premises conclusion =
  Option.is_some (
    List.fold_left2
      (fun assignment pattern formula_node -> Option.bind assignment (unify pattern formula_node))
      (unify inference_conclusion conclusion IntMap.empty)
      inference_premises
      premises)

let infer inference premises conclusion =
  let premise_formulas = List.map snd premises in
  if not (matches inference premise_formulas conclusion) then failwith "Inference does not fit pattern";
  (
    Context.union_all (List.map fst premises),
    conclusion
  )

let intro_forall ~name f =
  let x = Var1.gen name in
  let (context, conclusion) = f x in
  if Context.has_free_var1 x context then failwith "free variable in context";
  (context, BaseFormula.Forall (name, bind_var1 x conclusion))

let elim_forall var (context, conclusion) =
  match conclusion with
    | BaseFormula.Forall (_, inner) -> (context, substitute_var1 var inner)
    | _ -> failwith "not a forall"

let intro_exists var (context, conclusion) =
  (context, BaseFormula.Exists (var.Var1.name, bind_var1 var conclusion))

let elim_exists var formula (context, conclusion) =
  if VarSets.mem_var1 var (free_vars conclusion) then failwith "free variable in conclusion";
  let context = Context.remove formula context in
  if Context.has_free_var1 var context then failwith "free variable in context";
  let exists_premise = BaseFormula.Exists (var.Var1.name, bind_var1 var formula) in
  (Context.add exists_premise context, conclusion)

let intro_forall2 ~arity ~name f =
  let p = Var2.gen arity name in
  let (context, conclusion) = f (Auto p) in
  if Context.has_free_var2 p context then failwith "free variable in context";
  (context, BaseFormula.Forall2 (arity, name, bind_pred p conclusion))

let substitute_pred pred depth = function
  | Formula.Apply (Bound index, args) when index = depth -> apply_predicate pred args
  | atom -> Atom atom

let elim_forall2 pred (context, conclusion) =
  match conclusion with
    | BaseFormula.Forall2 (arity, _, inner) ->
        if arity != arity_of_predicate pred then failwith "wrong arity";
        (context, BaseFormula.general_map (substitute_pred pred) inner)
    | _ -> failwith "not a forall"
