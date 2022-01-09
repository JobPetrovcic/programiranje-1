(* Pomožni tip, ki predstavlja mrežo *)

type 'a grid = 'a Array.t Array.t

(* Funkcije za prikaz mreže.
   Te definiramo najprej, da si lahko z njimi pomagamo pri iskanju napak. *)

(* Razbije seznam [lst] v seznam seznamov dolžine [size] *)
let chunkify size lst =
  let rec aux chunk chunks n lst =
    match (n, lst) with
    | _, [] when chunk = [] -> List.rev chunks
    | _, [] -> List.rev (List.rev chunk :: chunks)
    | 0, _ :: _ -> aux [] (List.rev chunk :: chunks) size lst
    | _, x :: xs -> aux (x :: chunk) chunks (n - 1) xs
  in
  aux [] [] size lst

let string_of_list string_of_element sep lst =
  lst |> List.map string_of_element |> String.concat sep

let string_of_nested_list string_of_element inner_sep outer_sep =
  string_of_list (string_of_list string_of_element inner_sep) outer_sep

let string_of_row string_of_cell row =
  let string_of_cells =
    row |> Array.to_list |> chunkify 3
    |> string_of_nested_list string_of_cell "" "│"
  in
  "┃" ^ string_of_cells ^ "┃\n"

let print_grid string_of_cell grid =
  let ln = "───" in
  let big = "━━━" in
  let divider = "┠" ^ ln ^ "┼" ^ ln ^ "┼" ^ ln ^ "┨\n" in
  let row_blocks =
    grid |> Array.to_list |> chunkify 3
    |> string_of_nested_list (string_of_row string_of_cell) "" divider
  in
  Printf.printf "┏%s┯%s┯%s┓\n" big big big;
  Printf.printf "%s" row_blocks;
  Printf.printf "┗%s┷%s┷%s┛\n" big big big

(* Funkcije za dostopanje do elementov mreže *)

let get_row (grid : 'a grid) (row_ind : int) = 
  Array.init 9 (fun col_ind -> grid.(row_ind).(col_ind))

let rows grid = List.init 9 (get_row grid)

let get_column (grid : 'a grid) (col_ind : int) =
  Array.init 9 (fun row_ind -> grid.(row_ind).(col_ind))

let columns grid = List.init 9 (get_column grid)

let get_box (grid : 'a grid) (box_ind : int) =
 Array.init 9 (fun square_ind -> grid.((box_ind/3) * 3 + (square_ind)/3).((box_ind mod 3) * 3 + (square_ind mod 3)))

let boxes grid = List.init 9 (get_box grid)

(* Funkcije za ustvarjanje novih mrež *)

(*let map_grid_xy (f : int -> int -> 'a -> 'b) (grid : 'a grid) : 'b grid = 
  Array.init 9 (fun row_ind -> (Array.init 9 (fun col_ind -> (f row_ind col_ind (grid.(row_ind).(col_ind))))))*)
let map_grid (f : 'a -> 'b) (grid : 'a grid) : 'b grid = Array.init 9 (fun row_ind -> (Array.init 9 (fun col_ind -> (f (grid.(row_ind).(col_ind))))))


let copy_grid (grid : 'a grid) : 'a grid = map_grid (fun x -> x) grid

let foldi_grid (f : int -> int -> 'a -> 'acc -> 'acc) (grid : 'a grid)
    (acc : 'acc) : 'acc =
  let acc, _ =
    Array.fold_left
      (fun (acc, row_ind) row ->
        let acc, _ =
          Array.fold_left
            (fun (acc, col_ind) cell ->
              (f row_ind col_ind cell acc, col_ind + 1))
            (acc, 0) row
        in
        (acc, row_ind + 1))
      (acc, 0) grid
  in
  acc

let row_of_string cell_of_char str =
  List.init (String.length str) (String.get str) |> List.filter_map cell_of_char

let grid_of_string cell_of_char str =
  let grid =
    str |> String.split_on_char '\n'
    |> List.map (row_of_string cell_of_char)
    |> List.filter (function [] -> false | _ -> true)
    |> List.map Array.of_list |> Array.of_list
  in
  if Array.length grid <> 9 then failwith "Nepravilno število vrstic";
  if Array.exists (fun x -> x <> 9) (Array.map Array.length grid) then
    failwith "Nepravilno število stolpcev";
  grid

(* Model za vhodne probleme *)

let get_my_box ((x, y) : (int * int)) grid = get_box grid ((x/3) * 3 + y/3)
let get_my_row ((x, y) : (int * int)) grid = get_row grid x
let get_my_column ((x, y) : (int * int)) grid = get_column grid y

(* Funkcija skopirana iz https://stackoverflow.com/questions/21674947/ocaml-deoptionalize-a-list-is-there-a-simpler-way *)
let deoptionalize l =
  let rec deopt acc = function
    | [] -> List.rev acc
    | None::tl -> deopt acc tl
    | Some x::tl -> deopt (x::acc) tl
  in 
  deopt [] l

let filled_adj (loc : (int * int)) (grid : int option grid) = deoptionalize (Array.to_list (Array.concat [get_my_box loc grid; get_my_row loc grid; get_my_column loc grid]))

type problem = { initial_grid : int option grid; thermo : (int * int) list list; arrows : ((int * int) * ((int * int) list)) list}

let print_problem problem : unit = print_grid (function None -> " " | Some digit -> string_of_int digit) problem.initial_grid

let get_arrows str = 
  let split = String.split_on_char '\n' str
  in
  let get_point s =
    ((Char.code s.[1] - Char.code '0'), (Char.code s.[3] - Char.code '0'))
  in 
  let rec get_points lst =
    match lst with
    | [] -> []
    | a :: tail -> get_point a :: (get_points tail)
  in 
  let sgn x =
    if x > 0 then 1
    else if x=0 then 0
    else -1
  in
  let fill_gap (sx, sy) (ex, ey) =
    let dx = sgn (ex-sx)
    and dy = sgn (ey-sy)
    in
    let rec aux st en=
      if st=en then []
      else (
        let (ox, oy)=st in
        let nst = (ox+dx,oy+dy) in
        nst :: (aux nst en)
      )
    in
    aux (sx, sy) (ex, ey)
  in
  let rec expand st lst =
    match lst with
    | [] -> []
    | a :: tail -> List.concat [fill_gap st a; expand a tail]
  in
  let check_arrow s =
    if String.length s >=3 && String.sub s 0 3 = "A: " then (
      let st =get_point (String.sub s 3 5) and other =get_points (String.split_on_char ';' (String.sub s 12 (String.length s - 12))) in
      Some(st, (expand st other)))
    else None
  in
  let rec aux strlst =
    match strlst with
    | [] -> []
    | a :: tail -> (
      match check_arrow (String.trim a) with 
      | None -> aux tail
      | Some(x) ->  x :: (aux tail))
  in aux split

let get_thermo str =
  let split = String.split_on_char '\n' str
  in
  let get_point s =
    ((Char.code s.[1] - Char.code '0'), (Char.code s.[3] - Char.code '0'))
  in 
  let rec get_points lst =
    match lst with
    | [] -> []
    | a :: tail -> get_point a :: (get_points tail)
  in 
  let check_thermo s =
    if String.length s >=3 && String.sub s 0 3 = "T: " then Some(get_points (String.split_on_char ';' (String.sub s 3 (String.length s - 3))))
    else None
  in
  let rec aux strlst =
    match strlst with
    | [] -> []
    | a :: tail -> (
      match check_thermo (String.trim a) with 
      | None -> aux tail
      | Some(x) ->  x :: (aux tail))
  in aux split

let problem_of_string str =
  let cell_of_char = function
    | ' ' -> Some None
    | c when '1' <= c && c <= '9' -> Some (Some (Char.code c - Char.code '0'))
    | _ -> None
  in
  let basic_length = 358
  in
  let basic_problem = String.sub str 0 basic_length and
  extra_problem = String.sub str basic_length (String.length str - basic_length)
  in
  { initial_grid = grid_of_string cell_of_char basic_problem; thermo = get_thermo extra_problem; arrows = get_arrows extra_problem}

(* Model za izhodne rešitve *)

type solution = int grid

let print_solution (sol: solution) = print_grid string_of_int sol

(* Predpostvka, da so elementi od 1 do 9. 
Imamo tri možnosti: 
- O(n): inicializiramo nov array, in preštejemo koliko je vsakega elementa,
- O(n log n) sortiramo array nato preverimo arr.(i)=i+1,
- O(n^2) pregledamo pare elementov arr.(i)!=arr.(j),

ker je n=9, je težko teoretično ugotoviti, katera je najboljša, saj je za tako majhne n-je konstanta pomembna in je odvisna
od naše in Ocamlove implementacije.
*)

let is_permutation (arr : int array) : bool = 
  let cnt = Array.init 10 (fun x-> 0) in
  let rec aux ind =
    if (ind=9) then true
    else if cnt.(arr.(ind))=0 then (
      cnt.(arr.(ind)) <- 1;
      aux (ind+1)
    )
    else false
  in aux 0

let rec check_list_of_arrays lst=
  match lst with
  | [] -> true
  | (arr :: rep) -> if (is_permutation arr) then check_list_of_arrays rep else false

let is_sub (initial : int option array) (final : int array)=
  let rec aux ind =
    if ind=9 then true
    else if (initial.(ind)=None) then true
    else if (initial.(ind)=Some (final.(ind))) then true
    else false
  in aux 0

let rec is_sub_list initial final =
  match (initial, final) with
  | ([], []) -> true
  | (p1 :: rep1, p2 :: rep2) -> if (is_sub p1 p2) then is_sub_list rep1 rep2 else false
  | _ -> failwith "Pri preverjanju, da je rešitev res izpeljana iz začetne mreže je prišlo do napake."


let valid_thermo solution thermo =
  let rec is_increasing lst =
    match lst with
    | a :: b :: tail -> (
      let (xa, ya)= a and (xb, yb) = b in
      if solution.(xa).(ya) < solution.(xb).(yb) then is_increasing (b :: tail)
      else false
      
    )
    | _ -> true
  in
  let rec aux lst_lst =
    match lst_lst with
    | [] -> true
    | a :: tail ->(
      if is_increasing a then aux tail
      else false
    ) 
  in aux thermo

let valid_arrows solution arrows =
  let rec get_sum lst =
    match lst with
    | [] -> 0
    | a :: tail -> let (x, y) =a in solution.(x).(y) + get_sum tail
  in
  let rec is_sum arrow =
    let (par, chs) = arrow 
    in
    let (x, y) = par
    in
    get_sum chs = solution.(x).(y)
  in
  let rec aux lst_lst =
    match lst_lst with
    | [] -> true
    | a :: tail ->(
      if is_sum a then aux tail
      else false
    ) 
  in aux arrows

let is_valid_solution problem solution = 
  let initial_rs = rows problem.initial_grid and rs= rows solution and bs = boxes solution and cs=columns solution 
  in 
  let valid_basic = (is_sub_list initial_rs rs && check_list_of_arrays rs && check_list_of_arrays bs && check_list_of_arrays cs)
  in
  if List.length problem.thermo > 0 then valid_basic && valid_thermo solution problem.thermo
  else if List.length problem.arrows > 0 then valid_basic && valid_arrows solution problem.arrows
  else valid_basic
