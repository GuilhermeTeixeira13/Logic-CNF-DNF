open Scanf;;
open Printf;;

(* Cabeçalho a incluir *)

type formula =
  | Lit of char
  | Neg of char
  | Conj of formula * formula
  | Disj of formula * formula

let rec compare_formula f_1 f_2 =
  match (f_2, f_1) with
  | Lit c_1, Lit c_2 | Neg c_1, Neg c_2 -> Char.compare c_1 c_2
  | Lit c_1, Neg c_2 when c_1 = c_2 -> -1
  | Neg c_1, Lit c_2 when c_1 = c_2 -> 1
  | (Lit c_1 | Neg c_1), (Lit c_2 | Neg c_2) -> Char.compare c_1 c_2
  | (Lit _ | Neg _), (Disj _ | Conj _) -> -1
  | (Disj _ | Conj _), (Lit _ | Neg _) -> 1
  | Conj (f_1_1, f_1_2), Conj (f_2_1, f_2_2)
  | Disj (f_1_1, f_1_2), Disj (f_2_1, f_2_2) ->
      let c = compare_formula f_1_1 f_2_1 in
      if c = 0 then compare_formula f_1_2 f_2_2 else c
  | Conj _, Disj _ | Disj _, Conj _ -> 0

let rec normalize_conjs acc f_1 f_2 =
  match (f_1, f_2) with
  | Conj (f_1_1, f_1_2), Conj (f_2_1, f_2_2) ->
      normalize_conjs (normalize_conjs acc f_1_1 f_1_2) f_2_1 f_2_2
  | (Lit _ | Neg _ | Disj _), Conj (f_1', f_2') ->
      normalize_conjs (normalize_formula f_1 :: acc) f_1' f_2'
  | Conj (f_1', f_2'), (Lit _ | Neg _ | Disj _) ->
      normalize_formula f_2 :: normalize_conjs acc f_1' f_2'
  | _ -> normalize_formula f_2 :: normalize_formula f_1 :: acc

and normalize_disjs acc f_1 f_2 =
  match (f_1, f_2) with
  | Disj (f_1_1, f_1_2), Disj (f_2_1, f_2_2) ->
      normalize_disjs (normalize_disjs acc f_1_1 f_1_2) f_2_1 f_2_2
  | (Lit _ | Neg _ | Conj _), Disj (f_1', f_2') ->
      normalize_disjs (normalize_formula f_1 :: acc) f_1' f_2'
  | Disj (f_1', f_2'), (Lit _ | Neg _ | Conj _) ->
      normalize_formula f_2 :: normalize_disjs acc f_1' f_2'
  | _ -> normalize_formula f_2 :: normalize_formula f_1 :: acc

and normalize_formula = function
  | (Lit _ | Neg _) as f -> f
  | Conj (f_1, f_2) -> (
      match normalize_conjs [] f_1 f_2 |> List.sort compare_formula with
      | x :: xs -> List.fold_left (fun f acc -> Conj (acc, f)) x xs
      | _ -> assert false)
  | Disj (f_1, f_2) -> (
      match normalize_disjs [] f_1 f_2 |> List.sort compare_formula with
      | x :: xs -> List.fold_left (fun f acc -> Disj (acc, f)) x xs
      | _ -> assert false)

exception Malformed

let normalize_disjs f =
  let rec aux acc = function
    | (Lit _ | Neg _ | Conj _) as f -> f :: acc
    | Disj (((Lit _ | Neg _ | Conj _) as f_1), f_2) -> aux (f_1 :: acc) f_2
    | Disj (Disj _, _) -> raise Malformed
  in
  aux [] f |> List.rev

let normalize_conjs f =
  let rec aux acc = function
    | (Lit _ | Neg _ | Disj _) as f -> f :: acc
    | Conj (((Lit _ | Neg _ | Disj _) as f_1), f_2) -> aux (f_1 :: acc) f_2
    | Conj (Conj _, _) -> raise Malformed
  in
  aux [] f |> List.rev

let string_of_formula =
  let rec aux conj disj f = function
    | Lit c -> f (Char.escaped c)
    | Neg c -> f ("!" ^ Char.escaped c)
    | Conj (f_1, f_2) ->
        aux true false
          (fun s_1 ->
            aux true false
              (fun s_2 ->
                f
                  (if conj then s_1 ^ " & " ^ s_2
                  else "(" ^ s_1 ^ " & " ^ s_2 ^ ")"))
              f_2)
          f_1
    | Disj (f_1, f_2) ->
        aux false true
          (fun s_1 ->
            aux false true
              (fun s_2 ->
                f
                  (if disj then s_1 ^ " | " ^ s_2
                  else "(" ^ s_1 ^ " | " ^ s_2 ^ ")"))
              f_2)
          f_1
  in
  aux false false (fun x -> x)

let print_formula f = normalize_formula f |> string_of_formula |> print_endline

(* Escreva a solução do problema a seguir *)

(* https://stackoverflow.com/questions/39335469/how-to-use-ocaml-scanf-module-to-parse-a-string-containing-integers-separated-by *)
let stdinLineToArray s =
  let stream = (Scanning.from_string s) in
  let rec do_parse acc =
    try
      do_parse (Scanf.bscanf stream " %d " (fun x -> x :: acc))
    with
      Scan_failure _ -> acc
    | End_of_file -> acc
  in Array.of_list (List.rev (do_parse []));;

(* Feito por nós *)
let criaTabelaVerdade k =
  let totalLinhas = int_of_float (2. ** k) in
  let numElementosLinha = int_of_float(k +. 1.) in
  let tabela = Array.init totalLinhas (fun i -> Array.make numElementosLinha 0) in
  for i = 0 to (totalLinhas-1) do
    tabela.(i) <- (stdinLineToArray (read_line()));
  done;
  tabela;;

let inList a l = List.mem a l;;

let tabela_valor1 tabela k forma =
  let totalLinhas = int_of_float (2. ** k) in
  let numElementosLinha = int_of_float (k +. 1.) in
  let cont = ref 0 in
  let positions = ref [] in
  let () =  
    for posTabela = 0 to (totalLinhas-1) do
      if(forma = "FND") then (
        if(tabela.(posTabela).(numElementosLinha-1) == 1) then (
          cont:=!cont+1;
          positions := !positions @ [posTabela];
        )
      ) else (
        if(tabela.(posTabela).(numElementosLinha-1) == 0) then (
          cont:=!cont+1;
          positions := !positions @ [posTabela];
        )
      )
    done;
  in
  let tabelaReduzida = Array.init !cont (fun i -> Array.make (numElementosLinha-1) 0) in (* array grande tam 3 com pequenos tam 3 *)
  let pos = ref 0 in
  for posTabela = 0 to (totalLinhas-1) do (* 0 a 7 *)
    if((inList posTabela !positions) == (true)) then (
        for posLinha = 0 to (numElementosLinha-2) do
          tabelaReduzida.(!pos).(posLinha) <- tabela.(posTabela).(posLinha);
        done;
        pos:=!pos+1;
    )
  done;
  tabelaReduzida;;
  

let constroiTabelaLetras tabelaDeVars forma =
  let letras = [|'a'; 'b'; 'c'; 'd'; 'e'; 'f'; 'g'; 'h'; 'i'; 'j'; 'k'; 'l'|] in
  let tabelaLetras = Array.init (Array.length tabelaDeVars) (fun i -> Array.make (Array.length tabelaDeVars.(0)) (Lit 'a')) in
  for posTabela = 0 to ((Array.length tabelaDeVars) - 1) do
    for posLinha = 0 to (Array.length tabelaDeVars.(0)-1) do
      if forma = "FND" then (
        if(tabelaDeVars.(posTabela).(posLinha) == 1) then (
          tabelaLetras.(posTabela).(posLinha) <- Lit letras.(posLinha)
        )
        else (
          tabelaLetras.(posTabela).(posLinha) <- Neg letras.(posLinha)
        )
      ) else (
        if(tabelaDeVars.(posTabela).(posLinha) == 0) then (
          tabelaLetras.(posTabela).(posLinha) <- Lit letras.(posLinha)
        )
        else (
          tabelaLetras.(posTabela).(posLinha) <- Neg letras.(posLinha)
        )
      )        
    done;
  done;
  tabelaLetras;;


(* Dada uma lista de fórmulas, conjuga todos os elementos da lista e devolve a fórmula correspondente *)
let conjugaLista (lista: formula list) : formula =
  let conjugar a b = Conj(a,b) in
  let listaSemPrimeiroElemento = List.tl lista in 
  let f = List.fold_left conjugar (List.hd lista) listaSemPrimeiroElemento in
  f;;


let k = read_float();;
let tabelaVerdade = criaTabelaVerdade k;;


