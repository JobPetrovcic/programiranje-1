type available = { loc : int * int; possible : int list }

(* TODO: tip stanja ustrezno popravite, saj boste med reševanjem zaradi učinkovitosti
   želeli imeti še kakšno dodatno informacijo *)
type state = { problem : Model.problem; current_grid : int option Model.grid; unfilled : available list }

let print_state (state : state) : unit =
  Model.print_grid
    (function None -> "?" | Some digit -> string_of_int digit)
    state.current_grid;
  let rec aux lst =
    match lst with
    | [] -> ()
    | a :: other -> (let (x, y) =a.loc in Printf.printf "%d %d :" x y; List.iter (Printf.printf "%d ") a.possible;Printf.printf "\n";aux other)
  in
  aux state.unfilled

type response = Solved of Model.solution | Unsolved of state | Fail of state

let alloptions = List.init 9 (fun x -> x+1)
let get_options grid =
  let rec aux x y grid =
    if x=9 then []
    else if y=9 then aux (x+1) 0 grid
    else match grid.(x).(y) with
      | None -> {loc = (x, y); possible = alloptions} :: aux x (y+1) grid
      | Some digit -> aux x (y+1) grid
  in aux 0 0 grid

let clean_state (state : state) : state =
  let cmp (a : available) (b : available) : int =
    let sa = List.length a.possible and sb = List.length b.possible in
    if sa == sb then 0
    else if sa > sb then 1
    else -1
  in
  let rec isin el lst = 
    match lst with
    | [] -> false
    | a:: tail -> if(a=el) then true else isin el tail
  in
  let rec clean_list lst forbidden = 
    match lst with
    | [] -> []
    | a :: tail -> if isin a forbidden then clean_list tail forbidden else a :: clean_list tail forbidden
  in
  let rec aux (unfilled : available list) =
    match unfilled with 
    | [] -> []
    | av :: other_unfilled -> (
      let forbidden = Model.filled_adj av.loc state.current_grid in
      {loc = av.loc; possible=(clean_list av.possible forbidden)} :: aux other_unfilled)
  in
  {problem = state.problem; current_grid = state.current_grid; unfilled = List.sort cmp (aux state.unfilled)}

let initialize_state (problem : Model.problem) : state =
  clean_state { current_grid = Model.copy_grid problem.initial_grid; problem; unfilled = get_options problem.initial_grid}

let validate_state (state : state) : response =
  let unsolved =
    Array.exists (Array.exists Option.is_none) state.current_grid
  in
  if unsolved then Unsolved state
  else
    (* Option.get ne bo sprožil izjeme, ker so vse vrednosti v mreži oblike Some x *)
    let solution = Model.map_grid Option.get state.current_grid in
    if Model.is_valid_solution state.problem solution then Solved solution
    else Fail state

let apply (x, y) num grid =
  grid.(x).(y) <- Some(num);grid

let rec branch_state (state : state) : (state * state) option =
  match state.unfilled with 
  | [] -> Some(state, state)
  | unfilled_square :: other_unfilled -> (
    match unfilled_square with
    | {loc=loc; possible = []} -> None
    | {loc=loc; possible = [possibility]} -> branch_state (clean_state {problem = state.problem; current_grid = (apply loc possibility (Model.copy_grid state.current_grid)); unfilled = other_unfilled})
    | {loc=loc; possible = possibility :: other} -> ( Some (
        clean_state {problem = state.problem; current_grid = (apply loc possibility (Model.copy_grid state.current_grid)); unfilled = other_unfilled}, 
        {problem = state.problem; current_grid = Model.copy_grid state.current_grid; unfilled= {loc; possible = other}:: other_unfilled})
  ))

(* pogledamo, če trenutno stanje vodi do rešitve *)
let rec solve_state (state : state) =
  
  (* uveljavimo trenutne omejitve in pogledamo, kam smo prišli *)
  (* TODO: na tej točki je stanje smiselno počistiti in zožiti možne rešitve *)
  (* ta korak je izveden v branch_state *)
  match validate_state state with
  | Solved solution ->
      (* če smo našli rešitev, končamo *)
      Some solution
  | Fail fail ->
      (* prav tako končamo, če smo odkrili, da rešitev ni *)
      None
  | Unsolved state' ->
      (* če še nismo končali, raziščemo stanje, v katerem smo končali *)
      explore_state state'

and explore_state (state : state) =
  (* pri raziskovanju najprej pogledamo, ali lahko trenutno stanje razvejimo *)
  match branch_state state with
  | None ->
      (* če stanja ne moremo razvejiti, ga ne moremo raziskati *)
      None
  | Some (st1, st2) -> (
      (* če stanje lahko razvejimo na dve možnosti, poizkusimo prvo *)
      match solve_state st1 with
      | Some solution ->
          (* če prva možnost vodi do rešitve, do nje vodi tudi prvotno stanje *)
          Some solution
      | None ->
          (* če prva možnost ne vodi do rešitve, raziščemo še drugo možnost *)
          solve_state st2 )

let solve_problem (problem : Model.problem) =
  problem |> initialize_state |> solve_state
