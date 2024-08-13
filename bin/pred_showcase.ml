module P = Logic.Verifier.Pattern

module Name = struct
  type t = string
  let compare = String.compare
  let to_string x = x
end

module V = Logic.Verifier.Make(Name)

let example_1 = V.(
  let x_eq_x = equal "x" "x" in
  let p_imp_p = conn(Implies(x_eq_x, x_eq_x)) in
  let gen_p_imp_p = forall "x" p_imp_p in
  let proof = intro_forall "x" (assuming x_eq_x (fun p -> p)) in
  (gen_p_imp_p, proof)
)

let example_2 = V.(P.(
  let subset a b = forall "x" (conn(Implies(member "x" a, member "x" b))) in
  let a_ss_b_ss_c = conn(And(subset "a" "b", subset "b" "c")) in
  let claim = forall "a" (forall "b" (forall "c" (conn(Implies(a_ss_b_ss_c, subset "a" "c"))))) in

  let conj_1 = inference [Conn(And(MetaVar 1, MetaVar 2))] (MetaVar 1) in
  let conj_2 = inference [Conn(And(MetaVar 1, MetaVar 2))] (MetaVar 2) in
  let m_p = inference [Conn(Implies(MetaVar 1, MetaVar 2)); MetaVar 1] (MetaVar 2) in
  let proof = intro_forall "a" (intro_forall "b" (intro_forall "c" (assuming a_ss_b_ss_c (fun p ->
    let a_ss_b = infer conj_1 [p] (subset "a" "b") in
    let b_ss_c = infer conj_2 [p] (subset "b" "c") in
    let a_ss_c = assuming (member "x" "a") (fun x_in_a -> 
      let x_in_b = infer m_p [elim_forall "x" a_ss_b; x_in_a] (member "x" "b") in
      let x_in_c = infer m_p [elim_forall "x" b_ss_c; x_in_b] (member "x" "c") in
      x_in_c
    ) in
    intro_forall "x" a_ss_c
  )))) in

  (claim, proof)
))

let example_3 = V.(P.(
  let tautology = conn(Or(member "x" "y", conn(Not(member "x" "y")))) in
  let claim = forall "x" (forall "y" tautology) in

  let p_or_not_p = inference [] (Conn(Or(MetaVar 0, Conn(Not(MetaVar 0))))) in
  let proof = intro_forall "x" (intro_forall "y" (infer p_or_not_p [] tautology)) in

  (claim, proof)
))

let validate (claim, proof) =
  assert (V.does_prove proof claim);
  Printf.printf "Verified: %s\n" (V.string_of_formula claim)

let main () =
  validate example_1;
  validate example_2;
  validate example_3;
