open Scanf;;

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

(* Contador de linhas na tabela, cuja f é 1 ou 0, FND e FNC, respetivamente *)
let contadorParcelas (tabela: int array array) (k: float) (forma: string): int =
  let k_inteiro = int_of_float (k) in
  let len1 = Array.length tabela in
  let countlinhas = ref 0 in
  for i = 0 to (len1 -1 ) do
    if forma = "FND" then (
      if tabela.(i).(k_inteiro) == 1 then (
        countlinhas := !countlinhas + 1)
      else 
      if tabela.(i).(k_inteiro) == 0  then (
        countlinhas := !countlinhas + 0)
    )
    else (
      if forma = "FNC" then (
        if tabela.(i).(k_inteiro) == 0 then (
          countlinhas := !countlinhas + 1)
        else 
        if tabela.(i).(k_inteiro) == 1  then (
          countlinhas := !countlinhas + 0)
      )
    )
  done;
  !countlinhas;;

let tabela_seletiva (tabela: int array array) (k: float) (len_tabelaseletiva: int) (forma: string): (int array array) =
  let k_inteiro = int_of_float (k) in
  let arraySeletivo = Array.init (len_tabelaseletiva) (fun i -> Array.make k_inteiro 0) in
  let len_tabela = Array.length tabela in
  let incrementador = ref 0 in
  for i = 0 to (len_tabela - 1) do
    if forma = "FND" then (
      if tabela.(i).(k_inteiro) == 1 then  
        (for j = 0 to (k_inteiro-1) do
           arraySeletivo.(!incrementador).(j) <- tabela.(i).(j);
         done;
         incrementador := !incrementador + 1))
    else (
      if forma = "FNC" then (
        if tabela.(i).(k_inteiro) == 0 then  
        (for j = 0 to (k_inteiro-1) do
           arraySeletivo.(!incrementador).(j) <- tabela.(i).(j);
         done;
         incrementador := !incrementador + 1)
      )
    )
  done;
  arraySeletivo;;

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
let conjuntaLista (lista: formula list) : formula =
  let disjuntar a b = Conj(a,b) in
  let listaSemPrimeiroElemento = List.tl lista in 
  let f = List.fold_left disjuntar (List.hd lista) listaSemPrimeiroElemento in
  f;;

(* Dada uma lista de fórmulas, conjuga todos os elementos da lista e devolve a fórmula correspondente *)
let disjuntaLista (lista: formula list) : formula =
  let disjuntar a b = Disj(a,b) in
  let listaSemPrimeiroElemento = List.tl lista in 
  let f = List.fold_left disjuntar (List.hd lista) listaSemPrimeiroElemento in
  f;;


let armazena_expressoesarray (tabelaLetras: formula array array) (forma: string): (formula array) =
  let len_tabelaletras = Array.length tabelaLetras in
  let array_expressoes = Array.make len_tabelaletras (Lit 'a') in
  for i = 0 to (len_tabelaletras - 1) do
    if forma = "FND" then (
    array_expressoes.(i) <- (conjuntaLista(Array.to_list tabelaLetras.(i)));
    )
    else (
      if forma = "FNC" then (
        array_expressoes.(i) <- (disjuntaLista(Array.to_list tabelaLetras.(i)));
      )
    )
  done;
  array_expressoes;;


let expressao (array_expressoes: formula array) (forma: string): (formula) = 
  let conv_list = Array.to_list (array_expressoes) in
  if forma = "FND" then
    disjuntaLista(conv_list)
  else 
    conjuntaLista(conv_list);;

    


let k = read_float();;
let tabelaVerdade = criaTabelaVerdade k;;
let tabelaSeletivaFND = tabela_seletiva tabelaVerdade k (contadorParcelas tabelaVerdade k "FND") "FND";;
let tabelaSeletivaFNC = tabela_seletiva tabelaVerdade k (contadorParcelas tabelaVerdade k "FNC") "FNC";;
let tabelaLetrasFND = constroiTabelaLetras tabelaSeletivaFND "FND";;
let tabelaLetrasFNC = constroiTabelaLetras tabelaSeletivaFND "FNC";;
let armazena_expressoesarrayFND = armazena_expressoesarray tabelaLetrasFND "FND";;
let armazena_expressoesarrayFNC = armazena_expressoesarray tabelaLetrasFND "FNC";;
let expressaoFND = expressao armazena_expressoesarrayFND "FND";;
let expressaoFNC = expressao armazena_expressoesarrayFND "FNC";;
print_formula expressaoFND;;
print_formula expressaoFNC;;