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


(* 
  Input:
    . s -> string correspondente a uma linha que contém vários inteiros.

  Output:
    . (int array) -> Array com os inteiros presentes na string s.

  Fonte: https://stackoverflow.com/questions/39335469/how-to-use-ocaml-scanf-module-to-parse-a-string-containing-integers-separated-by 
*)

let stdinLineToArray s =
  let stream = (Scanning.from_string s) in
  let rec do_parse acc =
    try
      do_parse (Scanf.bscanf stream " %d " (fun x -> x :: acc))
    with
      Scan_failure _ -> acc
    | End_of_file -> acc
  in Array.of_list (List.rev (do_parse []));;


(* 
  Input:
    . k -> nº de variáveis da função booleana.
  
  Funcionamento:
    . Após o utilizador passar o nº de variáveis que deseja, efetua-se o cálculo do tamanho da tabela e guarda-se
    o nº de linhas na variável "nLinhas" e o nº de colunas na "nColunas".
    . É criado um array bi-dimensional, "tabela", com tamanho "nLinhas", que no seu interior, irá ter vários arrays de
    tamanho "nColunas" inicializados a 0.
    . É percorrido o array bi-dimensional, até à sua última posição, onde em cada posição é colocado o array resultante da função "stdinLineToArray (read_line())"

  Output:
    . (int array array) -> Array constituido por arrays de inteiros.

*)

let criaTabelaVerdade k =
  let nLinhas = int_of_float (2. ** k) in
  let nColunas = int_of_float(k +. 1.) in
  let tabela = Array.init nLinhas (fun i -> Array.make nColunas 0) in
  for i = 0 to (nLinhas-1) do
    tabela.(i) <- (stdinLineToArray (read_line()));
  done;
  tabela;;


(* 
  Nota: Esta função é auxiliar da função "tabela_seletiva", que lhe sucede.
  Input:
    . tabela -> array bi-dimensional, onde estão armazenados os valores passados pelo utilizador.
    . posvalorffloat -> posição onde se encontra o valor de f em cada linha da tabela, ou seja, última posição de cada array do array bi-dimensional, em float.
    . forma -> string "FNC" ou "FND".
  Funcionamento:
    .O algoritmo percorre o array bi-dimensional, tabela, posição a posição e:
      . Caso a forma seja FND:
        . Se encontrou um 1, na posição "posvalorf", soma um ao contador "nlinhasvalorf"
        . Se encontrou um 0, na posição "posvalorf", soma zero ao contador "nlinhasvalorf"
      . Caso a forma seja FNC:
        . Se encontrou um 1, na posição "posvalorf", soma 0 ao contador "nlinhasvalorf"
        . Se encontrou um 0, na posição "posvalorf", soma 1 ao contador "nlinhasvalorf"
  Output:
    . (int) -> Nº de arrays do array bi-dimensional, cuja última posição desses, é 1 ou 0. Queremos o nº de linhas que, em cada linha da tabela, a sua última coluna é 1 ou 0, caso seja, FND ou FNC, respetivamente.
*)

let contadorLinhasComValorf (tabela: int array array) (posvalorffloat: float) (forma: string): int =
  let posvalorf = int_of_float (posvalorffloat) in
  let len_tabela = Array.length tabela in
  let nlinhasvalorf = ref 0 in
  for i = 0 to (len_tabela -1 ) do
    if forma = "FND" then (
      if tabela.(i).(posvalorf) == 1 then (
        nlinhasvalorf := !nlinhasvalorf + 1)
      else 
      if tabela.(i).(posvalorf) == 0  then (
        nlinhasvalorf := !nlinhasvalorf + 0)
    )
    else (
      if forma = "FNC" then (
        if tabela.(i).(posvalorf) == 0 then (
          nlinhasvalorf := !nlinhasvalorf + 1)
        else 
        if tabela.(i).(posvalorf) == 1  then (
          nlinhasvalorf := !nlinhasvalorf + 0)
      )
    )
  done;
  !nlinhasvalorf;;


(* 
  Input:
    . tabela -> array bi-dimensional, onde estão armazenados os valores passados pelo utilizador.
    . posvalorffloat -> posição onde se encontra o valor de f em cada linha da tabela, ou seja, última posição de cada array do array bi-dimensional, em float.
    . nlinhasvalorf -> Nº de arrays do array bi-dimensional, cuja última posição desses, é 1 ou 0, caso seja, FND ou FNC, respetivamente.
    . forma -> string "FNC" ou "FND".
  Funcionamento:
    . É criado o "arraySeletivo", int array array, onde iram ser armazenados somente as linhas cujo valor, na última coluna, de cada, seja 1 ou 0, caso seja, FND e FNC, respetivamente. Este, tem menos uma coluna que a tabela(todas menos aquela onde é armazenado o valor de f), e o nº linhas que a função antecedora "contadorLinhasComValorf" retornou. 
    .O algoritmo percorre o array bi-dimensional, tabela, posição a posição e:
      . Caso a forma seja FND:
        . Se encontrou um 1, na posição "posvalorf":
            . Percorre o "arraySeletivo", posição a posição e:
              . Armazena os arrays do array bi-dimensional sem a última posição e onde, estes tinham, nessa última posição, valor um.
      . Caso a forma seja FNC:
        . Se encontrou um 0, na posição "posvalorf":
            . Percorre o "arraySeletivo", posição a posição e:
              . Armazena os arrays do array bi-dimensional sem a última posição e onde, estes tinham, nessa última posição, valor zero.
  Output:
    . (int array array) -> "arraySeletivo", que tem de tamanho o nº linhas que a função antecedora "contadorLinhasComValorf" retornou e armazena só arrays cujo f é 0 ou 1, sem esta coluna f.
*)

let tabela_seletiva (tabela: int array array) (posvalorffloat: float) (nlinhasvalorf: int) (forma: string): (int array array) =
  let posvalorf = int_of_float (posvalorffloat) in
  let arraySeletivo = Array.init (nlinhasvalorf) (fun i -> Array.make posvalorf 0) in
  let len_tabela = Array.length tabela in
  let incrementador = ref 0 in
  for i = 0 to (len_tabela - 1) do
    if forma = "FND" then (
      if tabela.(i).(posvalorf) == 1 then  
        (for j = 0 to (posvalorf-1) do
           arraySeletivo.(!incrementador).(j) <- tabela.(i).(j);
         done;
         incrementador := !incrementador + 1))
    else (
      if forma = "FNC" then (
        if tabela.(i).(posvalorf) == 0 then  
        (for j = 0 to (posvalorf-1) do
           arraySeletivo.(!incrementador).(j) <- tabela.(i).(j);
         done;
         incrementador := !incrementador + 1)
      )
    )
  done;
  arraySeletivo;;


(* 
  Input: 
    . tabelaDeVars -> (int array array) (tabela sem o resultado da função, pois não interessa para o caso),
    correspondente às linhas da tabela da verdade onde o resultado da função é 1 (caso FND), ou 0 (caso FNC).
    . forma -> Uma dada string "FNC" ou "FND".

  Funcionamento:
    É criado um (formula array array), chamado tabelaLetras, do mesmo tamanho do (array array int)
    O algoritmo percorre o (array array int) posição a posição e:
      . Caso a forma seja FND:
        . Se encontrou um 1, então é adicionado à tabelaLetras o Lit do char correspondente à variável. (x1->'a', x2->'b' ...)
        . Se encontrou um 0, então é adicionado à tabelaLetras o Neg do char correspondente à variável.
      . Caso a forma seja FNC:
        . Se encontrou um 1, então é adicionado à tabelaLetras o Neg do char correspondente à variável.
        . Se encontrou um 0, então é adicionado à tabelaLetras o Lit do char correspondente à variável.

  OUTPUT:
    . tabelaDeLetras (formula array array)
*)
let constroiTabelaLetras tabelaDeVars forma =
  let letras = [|'a'; 'b'; 'c'; 'd'; 'e'; 'f'; 'g'; 'h'; 'i'; 'j'; 'k'; 'l'|] in
  let totalLinhas = Array.length tabelaDeVars in
  let totalColunas = Array.length tabelaDeVars.(0) in
  let tabelaLetras = Array.init (totalLinhas) (fun i -> Array.make (totalColunas) (Lit 'a')) in
  for linha = 0 to (totalLinhas - 1) do
    for coluna = 0 to (totalColunas - 1) do
      if forma = "FND" then (
        if(tabelaDeVars.(linha).(coluna) == 1) then (
          tabelaLetras.(linha).(coluna) <- Lit letras.(coluna)
        )
        else (
          tabelaLetras.(linha).(coluna) <- Neg letras.(coluna)
        )
      ) else (
        if(tabelaDeVars.(linha).(coluna) == 0) then (
          tabelaLetras.(linha).(coluna) <- Lit letras.(coluna)
        )
        else (
          tabelaLetras.(linha).(coluna) <- Neg letras.(coluna)
        )
      )        
    done;
  done;
  tabelaLetras;;

(*
  Input: 
    . lista -> (formula list) Lista de fórmulas que se prentende conjugar.

  Funcionamento:
    A lista é varrida e ao mesmo tempo conjugada, exemplo:

    Dada uma lista de fórmulas, por exemplo: [Lit 'a', Lit 'b', Neg 'c'], o que o algoritmo faz é o seguinte:
    
    fold conjugar (Lit 'a') [Lit 'b', Neg 'c']
    fold conjugar (conjugar Lit'a' Lit'b') [Neg'c']
    fold conjugar (Conj(Lit'a', Lit'b')) [Neg 'c']
    fold conjugar (conjugar Conj(Lit'a', Lit'b') Neg 'c') []
    fold conjugar (Conj(Conj(Lit'a', Lit'b'), Neg 'c')) []

    return formula -> Conj(Conj(Lit'a', Lit'b'), Neg 'c')

  OUTPUT:
    . formula -> (formula) correspondente à conjunção das fórmulas presentes na lista
    passada como input.
  
  Fonte: Baseamo-nos no seguinte vídeo para elaborar um esboço de resolução do problema:
  https://www.youtube.com/watch?v=Zq1QJ2QztgM
*)
let conjugaLista (lista: formula list) : formula =
  let conjugar a b = Conj(a,b) in
  let listaSemPrimeiroElemento = List.tl lista in 
  let primeiroElementoLista = List.hd lista in
  let f = List.fold_left conjugar primeiroElementoLista listaSemPrimeiroElemento in
  f;;

(*
  Input: 
    . lista -> (formula list) Lista de fórmulas que se pretende disjuntar.

  Funcionamento:
    Igual à função anterior só que para a disjunção.

  OUTPUT:
    . formula -> (formula) correspondente à disjunção das fórmulas presentes na lista
    passada como input.
  
  Fonte: Baseamo-nos no seguinte vídeo para elaborar um esboço de resolução do problema:
  https://www.youtube.com/watch?v=Zq1QJ2QztgM
*)
let disjuncaoLista (lista: formula list) : formula =
  let disjuncao a b = Disj(a,b) in
  let listaSemPrimeiroElemento = List.tl lista in 
  let primeiroElementoLista = List.hd lista in
  let f = List.fold_left disjuncao primeiroElementoLista listaSemPrimeiroElemento in
  f;;

(*
  Input: 
    . tabelaDeLetras -> (formula array array) Tabela com os literais.
    . forma -> Uma dada string "FNC" ou "FND".

  Funcionamento:
    . Caso a forma seja FND:
      . Conjuga cada linha e guarda cada linha 'formulada' num array.
    . Caso a forma seja FNC:
      . Faz a disjunção de cada linha e guarda cada linha 'formulada' num array.

  OUTPUT:
    . linhasFormuladas -> (formula array) array em que cada elemento contém a fórmula
    correspondente a uma linha da tabela.
  
  Fonte: Baseamo-nos no seguinte vídeo para elaborar um esboço de resolução do problema:
  https://www.youtube.com/watch?v=Zq1QJ2QztgM
*)
let formulasDasLinhas tabelaDeLetras forma =
  let linhasTabela = Array.length tabelaDeLetras in
  let linhasFormuladas = Array.make linhasTabela (Lit 'a') in
  for posTabela = 0 to (linhasTabela-1) do
    if(forma = "FND") then (
      linhasFormuladas.(posTabela) <- conjugaLista (Array.to_list (tabelaDeLetras.(posTabela)));
    )
    else (
      linhasFormuladas.(posTabela) <- disjuncaoLista (Array.to_list (tabelaDeLetras.(posTabela)));
    )  
    done;
  linhasFormuladas;;

(* CORPO DO PROGRAMA *)

let k = read_float();;

let tabelaVerdade = criaTabelaVerdade k;;

let tabelaSeletivaFND = tabela_seletiva tabelaVerdade k (contadorParcelas tabelaVerdade k "FND") "FND";;
let tabelaSeletivaFNC = tabela_seletiva tabelaVerdade k (contadorParcelas tabelaVerdade k "FNC") "FNC";;

let tabelaLetrasFND = constroiTabelaLetras tabelaSeletivaFND "FND";;
let tabelaLetrasFNC = constroiTabelaLetras tabelaSeletivaFNC "FNC";;

let arrayParcelasFND = formulasDasLinhas tabelaLetrasFND "FND";;
let arrayParcelasFNC = formulasDasLinhas tabelaLetrasFNC "FNC";;

let formulaFinalFND = disjuncaoLista (Array.to_list arrayParcelasFND);;
let formulaFinalFNC = conjugaLista (Array.to_list arrayParcelasFNC);;

print_formula formulaFinalFND;;
print_formula formulaFinalFNC;;

(* EXEMPLO DE FUNCIONAMENTO *)
