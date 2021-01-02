open Proj2_types;;

let buildParseTree (input : string list) : tree =                               
        let rec getSublist n lst = 
                match lst with
                | [] -> []
                | h::t ->           
                                if n = 0 && h <> "(" then lst
                                else if n = 0 && h = "(" then getSublist 1 t
                                else if h = "(" then h::(getSublist (n+1) t)
                                else if h = ")" && (n-1) = 0 then []
                                else if h = ")" then h::(getSublist (n-1) t)
                                else h::(getSublist n t)
        and getFstToken n lst = 
                match lst with
                | [] -> raise (Invalid_argument "Error 1")
                | h::t -> 
                                if n = 0 && h <> "(" && h <> ")" then h::[]
                                else if h = ")" && (n-1) = 0 then h::[]
                                else if h = ")" then h::(getFstToken (n-1) t)
                                else if h = "(" then h::(getFstToken (n+1) t)
                                else h::(getFstToken n t) 
        and getSndToken m n lst = 
                match lst with
                | [] -> raise (Invalid_argument "Error 2")
                | h::t -> 
                                if m = (-1) then 
                                        if h <> "(" then getSndToken 0 n t
                                        else getSndToken 1 n t
                                else if m >= 1 then 
                                        if h = "(" then getSndToken (m+1) n t
                                        else if h = ")" then getSndToken (m-1) n t
                                        else getSndToken m n t
                                else begin
                                        if n = 0 && h <> "(" && h <> ")" then h::[]
                                        else if h = ")" && (n-1) = 0 then h::[]
                                        else if h = ")" then h::(getSndToken 0 (n-1) t)
                                        else if h = "(" then h::(getSndToken 0 (n+1) t)
                                        else h::(getSndToken 0 n t) 
                                end
        in let rec sTag lst = 
                match lst with
                | [] -> raise (Invalid_argument "Error 3")
                | [x] ->TreeNode ("S", [TreeNode (x, [])])
                | h::t -> 
                        if h = "(" then
                                TreeNode ("S", [
                                        TreeNode ("(", []);
                                        TreeNode ("T", tTag (getSublist 0 (h::t)));
                                        TreeNode(")", [])])
                        else 
                                TreeNode ("S", [
                                        TreeNode (h, [])]) 
        and tTag lst = 
                match lst with
                | [] -> raise (Invalid_argument "Error 4")
                | h::t -> 
                        if h = "not" then [TreeNode(h, []); sTag (getFstToken 0 t)]
                        else [TreeNode(h, []); sTag (getFstToken 0 t); sTag (getSndToken (-1) 0 t)] 
        in sTag input;;

let rec buildAbstractSyntaxTree (input : tree) : tree = 
        match input with
        | TreeNode(str, lst) ->
                        if str = "S" then
                                match lst with
                                | [] -> raise (Invalid_argument "Error 5")
                                | [x;y;z] -> buildAbstractSyntaxTree y
                                | [x] -> x
                                | h::t -> raise (Invalid_argument "Error 6")  
                        else if str = "T" then
                                match lst with
                                | [] -> raise (Invalid_argument "Error 7")
                                | [x;y;z] ->
                                                (match x with
                                                | TreeNode(str, lst) ->
                                                                if str = "and" then TreeNode("and", [
                                                                        buildAbstractSyntaxTree y;
                                                                        buildAbstractSyntaxTree z])
                                                                else TreeNode("or", [
                                                                        buildAbstractSyntaxTree y;
                                                                        buildAbstractSyntaxTree z]))
                                | [x;y] -> TreeNode("not", [buildAbstractSyntaxTree y])
                                | h::t -> raise (Invalid_argument "Error 8")   
                        else raise (Invalid_argument "Error 9");;

let scanVariable (input : string list) : string list = 
        let rec isPresent lst n =
                match lst with
                | [] -> false
                | h::t ->
                                if h = n then true
                                else isPresent t n
        in let rec removeDuplicates lst =
                match lst with
                | [] -> []
                | h::t ->
                                let sub = removeDuplicates t in
                                if isPresent sub h then sub
                                else h::sub
                                in let getVariables lst = 
                                        let modifiedLst = removeDuplicates lst in
                                        let rec removeNonVar lst =
                                                match lst with 
                        | [] -> []
                        | h::t -> 
                                        if h = "a" || h = "b" || h = "c" ||  h = "d" ||  h = "e" ||  h = "f" || h = "g" || h = "h" ||
                                        h = "i" ||  h = "j" || h = "k" || h = "l" || h = "m" || h = "n" || h = "o" || h = "p" ||       
                                        h = "q" || h = "r" || h = "s" || h = "t" || h = "u" || h = "v" || h = "w" || h = "x" || 
                                        h = "y" || h = "z" then h :: removeNonVar t
                                else removeNonVar t
                                        in removeNonVar modifiedLst
                                        in getVariables input;;          

let rec generateInitialAssignList (varList : string list) : (string * bool) list = 
        match varList with
        | [] -> []
        | h :: t -> (h, false) :: generateInitialAssignList t;;

let generateNextAssignList (assignList : (string * bool) list) : (string * bool) list * bool = 
        let reverse lst = 
                let rec aux acc = function
                        | [] -> acc
                        | h::t -> aux (h::acc) t
                in aux [] lst
        in let reverseLst = reverse assignList
        in let rec generate (lst : (string * bool) list) (carry : bool) : (string * bool) list =
                match lst with
                | [] -> []
                | h::t ->
                                let str = fst h in 
                                let tf = snd h in
                                if carry then
                                        if tf then (str, false)::(generate t true)
                                        else (str, true)::(generate t false)
                                else (str, tf)::(generate t false)
        in let nextAssignLst = generate reverseLst true
        in let rec generateCarryValue (lst : (string * bool) list) : bool = 
                match lst with
                | [] -> true
                | h::t ->
                                let tf = snd h in
                                if tf then false && (generateCarryValue t)
                                else true && (generateCarryValue t)
        in ((reverse nextAssignLst), (generateCarryValue nextAssignLst));;

let rec lookupVar (assignList : (string * bool) list) (str : string) : bool = 
        match assignList with
        | [] -> raise (Invalid_argument "Error 12")
        | h :: t -> 
                        let var = fst h in
                        let tf = snd h in
                        if var = str then tf else lookupVar t str;;

let rec evaluateTree (t : tree) (assignList : (string * bool) list) : bool = 
        let rec matchVar str lst = 
                match lst with
                | [] -> raise (Invalid_argument "Error 13")
                | h::t -> 
                                let var = fst h in
                                let tf = snd h in
                                if str = var then tf else matchVar str t
                                in match t with
        | TreeNode (str, lst) ->
                        if str = "TRUE" then true
                        else if str = "FALSE" then false
                        else if str = "and" then
                                match lst with
                                | [] -> raise (Invalid_argument "Error 14")
                                | x::y::t -> (evaluateTree x assignList) && (evaluateTree y assignList)
                                | x::t -> raise (Invalid_argument "Error 15")
                        else if str = "or" then
                                match lst with
                                | [] -> raise (Invalid_argument "Error 16")
                                | x::y::t -> (evaluateTree x assignList) || (evaluateTree y assignList)
                                | x::t -> raise (Invalid_argument "Error 17")
                        else if str = "not" then
                                match lst with
                                | [] -> raise (Invalid_argument "Error 18")
                                | h::t -> not (evaluateTree h assignList)
                        else matchVar str assignList;;

let satisfiable (input : string list) : (string * bool) list list = 
        let initialList = generateInitialAssignList (scanVariable input)
        and astTree = buildAbstractSyntaxTree (buildParseTree input)
        in let rec evaluate (t : tree) (lst : (string * bool) list) : (string * bool) list list = 
                if (evaluateTree t lst) then
                        let nextLst = generateNextAssignList lst in
                        let subLst = fst nextLst in
                        let tf = snd nextLst in
                        if tf then [lst] else lst::(evaluate t subLst)
                else
                        let nextLst = generateNextAssignList lst in
                        let subLst = fst nextLst in
                        let tf = snd nextLst in
                        if tf then [] else (evaluate t subLst)
        in let resultLst = evaluate astTree initialList in
        match resultLst with
        | [] -> []
        | h::t -> resultLst;;

