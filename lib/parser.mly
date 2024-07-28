%token <String.t> LIDENT
%token <String.t> UIDENT
%token <String.t> QIDENT

%token EOF

%token COMMA
%token EQUALS
%token UNDERSCORE

%token LPAREN
%token RPAREN

%token NOT
%token AND
%token OR
%token IMPLIES

%left OR
%left AND
%right IMPLIES
%nonassoc NOT

%token ASSUME
%token FANTASY
%token JOIN
%token SEPARATE
%token DNEG_ADD
%token DNEG_REM
%token CONTRAPOSITIVE1
%token CONTRAPOSITIVE2
%token DETACHMENT
%token SWITCHEROO
%token DE_MORGAN

%{
module Proposition = Kernel.Proposition
module STab = Map.Make(String)

let empty = (STab.empty, [])

let props = ref empty
let judgs = ref empty

let define cref v t =
  let (tab, stack) = !cref in
  let tab' = STab.update v (function
                            | None -> Printf.fprintf stdout "Define %s\n" v; Some t
                            | Some _ -> failwith (Printf.sprintf "Cannot redefine %s" v))
                         tab
  and stack' = t :: stack
  in
  cref := (tab', stack')

let push cref v =
  let (tab, stack) = !cref in
  let stack' = v :: stack in
  cref := (tab, stack')

let last cref =
  let (_, stack) = !cref in
  List.hd stack

let getvar v cref =
  let (tab, _) = !cref in
  STab.find v tab

%}

%type <Kernel.String.t> Subproof
%type <Kernel.String.prop> Prop
%type <Kernel.String.t list> Step

%start <Kernel.String.t> proof


%%

proof:
  | reset_state proof_step+ EOF { last judgs }

reset_state:
  | {
      print_endline "\nReset state";
      judgs := empty;
      props := empty
    }
proof_step:
  | BuildProp
    {}
  | res = Step
    { List.iter (push judgs) res }
  | vs = separated_nonempty_list(COMMA, LIDENT); EQUALS; ts = Step
    { List.iter2 (fun v t -> match v with
                             | "_" -> ()
                             | _ -> define judgs v t)
                 vs ts
    }

Subproof:
  | UNDERSCORE { last judgs }
  | v = LIDENT { getvar v judgs }

Step:
  | ASSUME;  p = Prop   { [ Kernel.String.assume p ]  }
  | FANTASY; p = Prop; t = Subproof { [ Kernel.String.fantasy p t ] }
  | JOIN;    l = Subproof; r = Subproof { [ Kernel.String.join l r ]}
  | SEPARATE; t = Subproof { let l,r = Kernel.String.separate t in [l; r] }
  | DNEG_ADD; t = Subproof { [ Kernel.String.add_doubleneg t ]}
  | DNEG_REM; t = Subproof { [ Kernel.String.rem_doubleneg t ]}
  | CONTRAPOSITIVE1; t = Subproof { [ Kernel.String.contrapositive1 t ]}
  | CONTRAPOSITIVE2; t = Subproof { [ Kernel.String.contrapositive2 t ]}
  | DETACHMENT; l = Subproof; r = Subproof { [ Kernel.String.detachment l r ]}
  | SWITCHEROO; t = Subproof { [ Kernel.String.switcheroo t ]}
  | DE_MORGAN; t = Subproof { [ Kernel.String.de_morgan t ]}

BuildProp:
  | v = UIDENT; EQUALS; p = Prop { define props v p }

Prop:
  | UNDERSCORE { last props }
  | v = UIDENT
    { match getvar v props with
      | exception Not_found -> Proposition.mk_fun v []
      | p -> p
    }
  | LPAREN; p = Prop; RPAREN { p }
  | v = QIDENT { Proposition.mk_meta v }
  | NOT; p = Prop { Proposition.mk_not p }
  | l = Prop; AND; r = Prop { Proposition.mk_and l r }
  | l = Prop; OR; r = Prop { Proposition.mk_or l r }
  | l = Prop; IMPLIES; r = Prop { Proposition.mk_implies l r }
