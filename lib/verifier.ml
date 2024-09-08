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

module Formula = struct
  type 'a debruijn = Bound of int | Free of 'a

  type t =
    | Atom of atom
    | Op of t LogicOp.t
    | Forall of string * t
    | Exists of string * t
    | Forall2 of int * string * t

  and atom =
    | Apply of Var2.t debruijn * Var1.t debruijn list
    | ApplyDefinition of definition * Var1.t debruijn list * t Lazy.t

  and definition = {
    symbol : Var2.t;
    func : Var1.t debruijn list -> t;
  }

  let apply_definition defn args =
    assert (List.length args = defn.symbol.arity);
    ApplyDefinition (defn, args, lazy (defn.func args))

  let rec map_aux f depth = function
    | Atom atom -> Atom (f depth atom)
    | Op expr -> Op (LogicOp.map (map_aux f depth) expr)
    | Forall (name, inner) -> Forall (name, map_aux f (depth + 1) inner)
    | Exists (name, inner) -> Exists (name, map_aux f (depth + 1) inner)
    | Forall2 (arity, name, inner) -> Forall2 (arity, name, map_aux f (depth + 1) inner)

  let map f = map_aux f 0

  let on_var1 f depth = function
    | Apply (pred, args) -> Apply (pred, List.map (f depth) args)
    (* TODO: don't re-create the thunk if we get the exact same list of vars *)
    | ApplyDefinition (defn, args, _) -> apply_definition defn (List.map (f depth) args)

  let on_var2 f depth = function
    | Apply (pred, args) as application ->
        (match f depth pred with
          | None -> application
          | Some(func) -> func args)
    | ApplyDefinition (_, _, _) as application -> application

  let equal_debruijn equal x y =
    match x, y with
      | Bound i, Bound j -> i = j
      | Free x, Free y -> equal x y
      | _, _ -> false

  let rec equal formula1 formula2 =
    match (formula1, formula2) with
      | Atom (ApplyDefinition (defn1, args1, thunk1)), Atom (ApplyDefinition (defn2, args2, thunk2)) ->
          if defn1.symbol.ind = defn2.symbol.ind && List.for_all2 (equal_debruijn Var1.equal) args1 args2
            then true
            else equal (Lazy.force thunk1) (Lazy.force thunk2)
      | Atom (ApplyDefinition (_, _, thunk)), _ -> equal (Lazy.force thunk) formula2
      | _, Atom (ApplyDefinition (_, _, thunk)) -> equal formula1 (Lazy.force thunk)
      | Atom (Apply (pred1, args1)), Atom (Apply (pred2, args2)) ->
          (equal_debruijn Var2.equal) pred1 pred2 && List.for_all2 (equal_debruijn Var1.equal) args1 args2
      | Op expr, Op expr2 -> (
            match LogicOp.map2_unify equal expr expr2 with
              | Some outcomes -> LogicOp.collapse (&&) outcomes
              | None -> false
          )
      | Forall (_, formula1), Forall (_, formula2) -> equal formula1 formula2
      | Exists (_, formula1), Exists (_, formula2) -> equal formula1 formula2
      | Forall2 (_, _, formula1), Forall2 (_, _, formula2) -> equal formula1 formula2
      | _ -> false

  let kleisli f g x = Option.bind (f x) g

  let rec unify pattern formula assignment =
    match pattern, formula with
      | Pattern.MetaVar i, _ ->
          (match IntMap.find_opt i assignment with
            | Some formula' -> if equal formula formula' then Some assignment else None
            | None -> Some (IntMap.add i formula assignment))
      | Op pexpr, Op fexpr ->
          Option.bind
            (LogicOp.map2_unify unify pexpr fexpr)
            (fun expr -> LogicOp.collapse kleisli expr assignment)
      | _, Atom (ApplyDefinition (_, _, thunk)) ->
          unify pattern (Lazy.force thunk) assignment
      | _, _ -> None

  let matches (inference_premises, inference_conclusion) premises conclusion =
    Option.is_some (
      List.fold_left2
        (fun assignment pattern formula_node -> Option.bind assignment (unify pattern formula_node))
        (unify inference_conclusion conclusion IntMap.empty)
        inference_premises
        premises)

  let free_vars_of_args args =
    Var1Set.of_list (List.filter_map (function Free var -> Some var | Bound _ -> None) args)

  let free_vars_of_atom = function
    | Apply (pred, args) -> {
        VarSets.vars1 = free_vars_of_args args;
        VarSets.vars2 = match pred with Free var -> Var2Set.singleton var | Bound _ -> Var2Set.empty;
      }
    | ApplyDefinition (_, args, _) -> {
        VarSets.vars1 = free_vars_of_args args;
        VarSets.vars2 = Var2Set.empty;
      }

  let rec free_vars = function
    | Atom atom -> free_vars_of_atom atom
    | Op expr -> LogicOp.(collapse VarSets.union (map free_vars expr))
    | Forall (_, inner) -> free_vars inner
    | Exists (_, inner) -> free_vars inner
    | Forall2 (_, _, inner) -> free_vars inner

  (* TODO: handle name collisions *)
  let lookup_var_name names = function
    | Free var -> var.Var1.name
    | Bound index -> List.nth names index

  let atom_to_string names = function
    | Apply (pred, args) ->
        Printf.sprintf "%s(%s)"
          (match pred with Free var -> var.name | Bound index -> List.nth names index)
          (String.concat ", " (List.map (lookup_var_name names) args))
    (* | ApplyDefinition (_, _, thunk) -> to_string_aux names (Lazy.force thunk) *)
    | ApplyDefinition (defn, args, _) ->
        Printf.sprintf "%s(%s)"
          defn.symbol.name
          (String.concat ", " (List.map (lookup_var_name names) args))

  let rec to_string_aux names = function
    | Atom atom -> atom_to_string names atom
    | Op expr -> LogicOp.to_string (LogicOp.map (to_string_aux names) expr)
    | Forall (name, inner) -> Printf.sprintf "∀%s %s" name (to_string_aux (name :: names) inner)
    | Exists (name, inner) -> Printf.sprintf "∃%s %s" name (to_string_aux (name :: names) inner)
    | Forall2 (arity, name, inner) -> Printf.sprintf "∀%s/%d %s" name arity (to_string_aux (name :: names) inner)

  let to_string = to_string_aux []
end

module Predicate = struct
  type t =
    | Var of Var2.t
    | Definition of Formula.definition

  let replace_template_var param_inds depth = Formula.(function
    | Free var ->
        (match Var1Map.find_opt var param_inds with
          | Some (Free var) -> Free var
          | Some (Bound index) -> Bound (depth + index)
          | None -> Free var)
    | Bound index -> Bound index)

  let apply_template params template args =
    let param_inds = Var1Map.of_list (List.combine params args) in
    Formula.(map (on_var1 (replace_template_var param_inds)) template)

  let base_on_template arity f =
    let params = List.init arity (fun i -> Var1.gen (Printf.sprintf "x%d" (i + 1))) in
    apply_template params (f params)

  let make_definition ~arity ~name f =
    Definition {
      symbol = Var2.gen arity name;
      func = base_on_template arity f;
    }

  let apply_var var args =
    assert (List.length args = var.Var2.arity);
    Formula.(Apply (Free var, args))

  let apply = function
    | Var var -> apply_var var
    | Definition defn -> Formula.apply_definition defn

  let arity = function
    | Var var -> var.arity
    | Definition defn -> defn.symbol.arity

  let to_string = function
    | Var var -> Printf.sprintf "%s/%d" var.name var.arity
    | Definition defn ->
        let param_names = List.init defn.symbol.arity (fun i -> Printf.sprintf "x%d" (i + 1)) in
        let params = List.map (fun name -> Formula.Free (Var1.gen name))  param_names in
        Printf.sprintf "%s(%s) = %s"
          defn.symbol.name
          (String.concat ", " param_names)
          (Formula.to_string (defn.func params))
end

module Quantification = struct
  let bind_var1 var =
    let transform_var depth = function
      | Formula.Free x when Var1.equal x var -> Formula.Bound depth
      | v -> v
    in Formula.(map (on_var1 transform_var))

  let substitute_var1 var =
    let transform_var depth = function
      | Formula.Bound index when index = depth -> Formula.Free var
      | v -> v
    in Formula.(map (on_var1 transform_var))

  let apply var arity args =
    assert (List.length args = arity);
    Formula.(Apply (var, args))

  let bind_pred var =
    let transform_pred depth = function
      | Formula.Free pred when Var2.equal pred var -> Some (apply (Formula.Bound depth) var.arity)
      | _ -> None
    in Formula.(map (on_var2 transform_pred))

  let substitute_pred pred =
    let transform_pred depth = function
      | Formula.Bound index when index = depth -> Some (Predicate.apply pred)
      | _ -> None
    in Formula.(map (on_var2 transform_pred))

  let intro_forall var inner = Formula.Forall (var.Var1.name, bind_var1 var inner)
  let intro_exists var inner = Formula.Exists (var.Var1.name, bind_var1 var inner)
  let intro_forall2 var inner = Formula.Forall2 (var.Var2.arity, var.Var2.name, bind_pred var inner)

  let elim_forall var = function
    | Formula.Forall (_, inner) -> substitute_var1 var inner
    | _ -> failwith "not a forall"

  let elim_forall2 pred = function
    | Formula.Forall2 (arity, _, inner) ->
        if arity != Predicate.arity pred then failwith "wrong arity";
        substitute_pred pred inner
    | _ -> failwith "not a forall"
end

module Context = struct
  type t = (Formula.t * VarSets.t) list

  let singleton formula = [(formula, Formula.free_vars formula)]

  let rec add formula = function
    | [] -> singleton formula
    | (formula', _) :: context ->
        if Formula.equal formula formula'
          then context
          else add formula context

  let remove formula =
    List.filter (fun (formula', _) -> not (Formula.equal formula formula'))

  let has_free_var1 var =
    List.exists (fun (_, free_vars) -> VarSets.mem_var1 var free_vars)

  let has_free_var2 var =
    List.exists (fun (_, free_vars) -> VarSets.mem_var2 var free_vars)

  let union =
    List.fold_left (fun ctx (formula, _) -> add formula ctx)

  let union_all =
    List.fold_left union []
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
type predicate = Predicate.t
type formula = Formula.t
type judgement = Context.t * Formula.t

let make_builtin ~arity ~name = Predicate.Var (Var2.gen arity name)

let predicate_of_formula = Predicate.make_definition

let string_of_predicate = Predicate.to_string

let apply pred args =
  Formula.Atom (Predicate.apply pred (List.map (fun var -> Formula.Free var) args))

let and_ lhs rhs = Formula.(Op (And (lhs, rhs)))
let or_ lhs rhs = Formula.(Op (Or (lhs, rhs)))
let implies lhs rhs = Formula.(Op (Implies (lhs, rhs)))
let iff lhs rhs = Formula.(Op (Iff (lhs, rhs)))
let not_ inner = Formula.(Op (Not inner))

let forall ~name f =
  let x = Var1.gen name in
  Quantification.intro_forall x (f x)

let exists ~name f =
  let x = Var1.gen name in
  Quantification.intro_exists x (f x)

let forall2 ~arity ~name f =
  let p = Var2.gen arity name in
  Quantification.intro_forall2 p (f (Predicate.Var p))

let equal_formula = Formula.equal
let string_of_formula = Formula.to_string

let judgement_premises (context, _) =
  Seq.map (fun (premise, _) -> premise) (List.to_seq context)

let judgement_conclusion (_, conclusion) = conclusion

let string_of_judgement (context, conclusion) =
  Printf.sprintf "%s ⊢ %s"
    (String.concat ", " (List.map (fun (premise, _) -> Formula.to_string premise) context))
    (Formula.to_string conclusion)

let assume formula =
  (Context.singleton formula, formula)

let assuming assumption derivation =
  let (context, conclusion) = derivation (assume assumption) in
  (
    Context.remove assumption context,
    implies assumption conclusion
  )

let infer inference premises conclusion =
  let premise_formulas = List.map (fun (_, conclusion) -> conclusion) premises in
  if not (Formula.matches inference premise_formulas conclusion) then failwith "Inference does not fit pattern";
  let joint_context = Context.union_all (List.map (fun (context, _) -> context) premises) in
  (joint_context, conclusion)

let intro_forall ~name f =
  let x = Var1.gen name in
  let (context, conclusion) = f x in
  if Context.has_free_var1 x context then failwith "free variable in context";
  (context, Quantification.intro_forall x conclusion)

let elim_forall var (context, conclusion) =
  (context, Quantification.elim_forall var conclusion)

let intro_exists ~name (context, conclusion) =
  (context, Quantification.intro_exists (Var1.gen name) conclusion)

let elim_exists var formula (context, conclusion) =
  if VarSets.mem_var1 var (Formula.free_vars conclusion) then failwith "free variable in conclusion";
  let context = Context.remove formula context in
  if Context.has_free_var1 var context then failwith "free variable in context";
  let exists_premise = Quantification.intro_exists var formula in
  (Context.add exists_premise context, conclusion)

let intro_forall2 ~arity ~name f =
  let p = Var2.gen arity name in
  let (context, conclusion) = f (Predicate.Var p) in
  if Context.has_free_var2 p context then failwith "free variable in context";
  (context, Quantification.intro_forall2 p conclusion)

let elim_forall2 pred (context, conclusion) =
  (context, Quantification.elim_forall2 pred conclusion)
