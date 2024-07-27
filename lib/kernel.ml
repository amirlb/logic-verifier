module Proposition = struct
  module Base = struct
    type 'a t =
      | Atom of 'a
      | Not of 'a t
      | And of 'a t * 'a t
      | Or of 'a t * 'a t
      | Implies of 'a t * 'a t
                            [@@deriving map, ord]
  end
  include Base

  let rec to_string f t = match t with
    | Atom s -> f s
    | Not p -> Printf.sprintf "¬%s" (to_string f p)
    | And (p, q) -> Printf.sprintf "(%s ∧ %s)" (to_string f p) (to_string f q)
    | Or (p, q) -> Printf.sprintf "(%s ∨ %s)" (to_string f p) (to_string f q)
    | Implies (p, q) -> Printf.sprintf "(%s → %s)" (to_string f p) (to_string f q)

  
  let canonical (type a) (cmp : a -> a -> int) t =
    let module AMap = Map.Make(struct
                          type t = a
                          let compare = cmp
                        end) in
    let uniq = ref AMap.empty
    and perm = ref []
    and last = ref 0 in
    let aux a = match AMap.find_opt a !uniq with
      | Some i -> i
      | None -> let i = !last in
                begin
                  uniq := AMap.add a i !uniq;
                  perm := a :: !perm;
                  incr last;
                  i
                end
    in
    let t' = map aux t in
    t', (List.rev !perm)
end

module type ORDER_STRING = sig
  type t
  val compare : t -> t -> int
  val to_string : t -> String.t
end

module type S = sig
  type prop
  type t                        (* judgement *)

  val join : t -> t -> t
  val separate : t -> t * t
  val add_doubleneg : t -> t
  val rem_doubleneg : t -> t
  val assume : prop -> t
  val fantasy : prop -> t -> t
  val detachment : t -> t -> t
  val contrapositive1 : t -> t
  val contrapositive2 : t -> t
  val de_morgan : t -> t
  val switcheroo : t -> t
  val proof : t -> prop
end

module Make(A : ORDER_STRING) : S with type prop = A.t Proposition.t = struct
  type prop = A.t Proposition.t
  module Context = Set.Make(struct
                       type t = prop
                       let compare p p' = Proposition.compare A.compare p p'
                     end)
  type t = Judgement of Context.t * prop

  open Proposition.Base

  let to_string p = Proposition.to_string A.to_string p
  let compare p p' = Proposition.compare A.compare p p'

  let correct ctx p =
    let ctx_str = String.concat ", " (List.map to_string (Context.elements ctx)) in
    Printf.printf "%s ⊢ %s\n" ctx_str (to_string p);
    Judgement (ctx, p)

  let inference f (Judgement (ctx, p)) = correct ctx (f p)

  let join (Judgement (ctx1, p1)) (Judgement (ctx2, p2)) =
    correct (Context.union ctx1 ctx2) (And(p1, p2))

  let separate (Judgement (ctx, p)) = match p with
    | And (p1, p2) -> correct ctx p1, correct ctx p2
    | _ -> failwith "Not an And proposition"

  let add_doubleneg = inference (fun p -> Not (Not p))

  let rem_doubleneg = inference (function
    | Not (Not p) -> p
    | _ -> failwith "Not a double negation"
  )

  let assume p = correct (Context.singleton p) p

  let fantasy p (Judgement (ctx, q)) =
    correct (Context.remove p ctx) (Implies(p, q))

  let detachment (Judgement (ctx1, p)) (Judgement (ctx2, q)) = match q with
    | Implies (p1, p2) when compare p1 p = 0 ->
        correct (Context.union ctx1 ctx2) p2
    | _ -> failwith ("Not a detachment (" ^ to_string p ^ ", " ^ to_string q ^ ")")

  let contrapositive1 = inference (function
    | Implies (p1, p2) -> Implies(Not p2, Not p1)
    | _ -> failwith "Not an implication"
  )

  let contrapositive2 = inference (function
    | Implies (Not p1, Not p2) -> Implies(p2, p1)
    | _ -> failwith "Not a contrapositive"
  )

  let de_morgan = inference (function
    | And (Not p1, Not p2) -> Not(Or(p1, p2))
    | Or  (Not p1, Not p2) -> Not(And(p1, p2))
    | _ -> failwith "Not a De-morgan candidate"
  )

  let switcheroo = inference (function
    | Implies (Not p1, p2) -> Or (p1, p2)
    | Or (p1, p2) -> Implies (Not p1, p2)
    | _ -> failwith "Not a switcheroo candidate"
  )

  let proof (Judgement (ctx, p)) =
    if Context.is_empty ctx
      then p
      else failwith "Context is not empty"  
end

module String = Make(struct include String let to_string t = t end)
