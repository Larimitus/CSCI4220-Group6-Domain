(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse Expressession notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <StmtList> ::= <Stmt> ";" <stmList>
   
   M2: M( [[ Stmt_1 ; StmtList_1 ]], m) = M(StmtList_1, M(Stmt_1,m))
    
   M4: 
        M( itree(inode("StmtList",_),
                    [
                        Stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        StmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( StmtList, M(Stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "StmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("StmtList",_),
                    [
                        Stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        StmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( StmtList, M(Stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "StmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

(* Helper functions *)
fun pow(x, 0) = 1
  | pow(x, n) = x * pow(x, n-1);

(* Expressessions *)
fun E( itree(inode("Express",_),
                [
                    LogicOr
                ]
            ), 
        m
    ) = E(LogicOr, m)
 
  (* Logical Or *)
  | E( itree(inode("LogicOr",_),
                [
                    LogicOr,
                    itree(inode("||",_), [] ),
                    LogicAnd
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(LogicOr, m0)
        in
          if toBool(v1) then (Boolean true, m1)
          else
            let
              val (v2,m2) = E(LogicAnd,m1)
            in
              (Boolean(toBool(v1) orelse toBool(v2)), m2)
            end
        end
  
  | E( itree(inode("LogicOr",_),
                [
                    LogicAnd
                ]
            ),
        m
    ) = E(LogicAnd, m)
  
  (* Logical And *)
  | E( itree(inode("LogicAnd",_),
                [
                    LogicAnd,
                    itree(inode("&&",_), [] ),
                    LogicEqual
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(LogicAnd, m0)
        in
          if toBool(v1) then
            let
              val (v2,m2) = E(LogicEqual,m1)
            in
              (Boolean(toBool(v1) andalso toBool(v2)), m2)
            end
          else (Boolean false, m1)
        end
    
  | E( itree(inode("LogicAnd",_),
                [
                    LogicEqual
                ]
            ),
        m
    ) = E(LogicEqual, m)

  (* LogicEqual *)
  | E( itree(inode("LogicEqual",_),
                [
                    LogicEqual,
                    itree(inode("==",_), [] ),
                    RelOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(LogicEqual, m0)
          val (v2, m2) = E(RelOp, m1)
        in
            (Boolean(v1 = v2), m2)
        end
        
  | E( itree(inode("LogicEqual",_),
                [
                    LogicEqual,
                    itree(inode("!=",_), [] ),
                    RelOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(LogicEqual, m0)
          val (v2,m2) = E(RelOp, m1)
        in
          (Boolean(v1 <> v2), m2)
        end
        
  | E( itree(inode("LogicEqual",_),
                [
                    RelOp
                ]
            ),
        m
    ) = E(RelOp, m)
        
  (* RelOp *)
  | E( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode("<",_), [] ),
                    AddOp2
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp1, m0)
          val (v2,m2) = E(AddOp2, m1)
        in
          (Boolean(toInt(v1) < toInt(v2)), m2)
        end
        
  | E( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode("<=",_), [] ),
                    AddOp2
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp1, m0)
          val (v2,m2) = E(AddOp2, m1)
        in
          (Boolean(toInt(v1) <= toInt(v2)), m2)
        end
  
  | E( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode(">",_), [] ),
                    AddOp2
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp1, m0)
          val (v2,m2) = E(AddOp2, m1)
        in
          (Boolean(toInt(v1) > toInt(v2)), m2)
        end
        
  | E( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode(">=",_), [] ),
                    AddOp2
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp1, m0)
          val (v2,m2) = E(AddOp2, m1)
        in
          (Boolean(toInt(v1) >= toInt(v2)), m2)
        end
  
  | E( itree(inode("RelOp",_),
                [
                    AddOp
                ]
            ),
        m
    ) = E(AddOp, m)
  
  (* AddOp *)
  | E( itree(inode("AddOp",_),
                [
                    AddOp,
                    itree(inode("+",_), [] ),
                    MultiOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp, m0)
          val (v2,m2) = E(MultiOp, m1)
        in
          (Integer(toInt(v1) + toInt(v2)), m2)
        end
   
   | E( itree(inode("AddOp",_),
                [
                    AddOp,
                    itree(inode("-",_), [] ),
                    MultiOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(AddOp, m0)
          val (v2,m2) = E(MultiOp, m1)
        in
          (Integer(toInt(v1) - toInt(v2)), m2)
        end
        
  | E( itree(inode("AddOp",_),
                [
                    MultiOp
                ]
            ),
        m
    ) = E(MultiOp, m)
  
  (* MultiOp *)  
  | E( itree(inode("MultiOp",_),
                [
                    MultiOp,
                    itree(inode("*",_), [] ),
                    UniMin
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(MultiOp, m0)
          val (v2,m2) = E(UniMin, m1)
        in
          (Integer(toInt(v1) * toInt(v2)), m2)
        end
   
  | E( itree(inode("MultiOp",_),
                [
                    MultiOp,
                    itree(inode("/",_), [] ),
                    UniMin
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(MultiOp, m0)
          val (v2,m2) = E(UniMin, m1)
        in
          (Integer(toInt(v1) div toInt(v2)), m2)
        end
  
  | E( itree(inode("MultiOp",_),
                [
                    MultiOp,
                    itree(inode("%",_), [] ),
                    UniMin
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(MultiOp, m0)
          val (v2,m2) = E(UniMin, m1)
        in
          (Integer(toInt(v1) mod toInt(v2)), m2)
        end
  
  | E( itree(inode("MultiOp",_),
                [
                    UniMin
                ]
            ),
        m
    ) = E(UniMin, m)
    
  (* Unary Minus *)
  | E( itree(inode("UniMin",_),
                [
                    itree(inode("-",_), [] ),
                    UniMin
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(UniMin, m0)
        in
          (Integer(~(toInt(v1))), m1)
        end
  
  | E( itree(inode("UniMin",_),
                [
                    ExpOp
                ]
            ),
        m
    ) = E(ExpOp, m)
  
  (* ExpOp *)
  | E( itree(inode("ExpOp",_),
                [
                    Ops,
                    itree(inode("^",_), [] ),
                    ExpOp
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(ExpOp, m0)
          val (v2,m2) = E(Ops, m1)
        in
          (Integer(pow(toInt(v1),toInt(v2))), m2)
        end
  
  | E( itree(inode("ExpOp",_),
                [
                    Ops
                ]
            ),
        m
    ) = E(Ops, m)
  
  (* Ops *)
  | E( itree(inode("Ops",_),
                [
                    operation
                ]
            ),
        m
    ) = E(operation, m)
  
  | E( itree(inode("Ops",_),
                [
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) = E(Express, m)
  
  | E( itree(inode("Ops",_),
                [
                    itree(inode("|",_), [] ),
                    Express,
                    itree(inode("|",_), [] )
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(Express, m0)
        in
          (Integer(Int.abs(toInt(v1))), m1)
        end
  
  | E( itree(inode("Ops",_),
                [
                    itree(inode("not",_), [] ),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] )
                ]
            ),
        m0
    ) = let
          val (v1,m1) = E(Express, m0)
        in
          (Boolean(not(toBool(v1))), m1)
        end
  
  (* Identifier *)
  | E(itree(inode("identifier",_),
                [
                    id_node
                ]
            ),
        m
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m))
          val v = accessStore(loc, m)
        in
          (v, m)
        end
  
  (* Value *)
  | E( itree(inode("Value",_),
                [
                    itree(inode("true",_), [] )
                ]
            ),
        m
    ) = (Boolean true, m)
    
  | E( itree(inode("Value",_),
                [
                    itree(inode("false",_), [] )
                ]
            ),
        m
    ) = (Boolean false, m)
  
  | E( itree(inode("Value",_),
                [
                    integer
                ]
            ),
        m
    ) = let
          val v = getLeaf(integer)
          val v_int = valOf(Int.fromString(v))
        in
          (Integer v_int, m)
        end
  
  (* IncrDecr *)
  | E( itree(inode("IncrDecr",_), 
                [ 
                    itree(inode("++",_), [] ),
                    id_node
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val inc = Integer(toInt(v) + 1)
          val m1 = updateStore(loc, inc, m0)
        in
          (inc, m1)
        end
        
  | E(  itree(inode("IncrDecr",_), 
                [ 
                    itree(inode("--",_), [] ),
                    id_node
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val dec = Integer(toInt(v) - 1)
          val m1 = updateStore(loc, dec, m0)
        in
          (dec, m1)
        end
        
  | E(  itree(inode("IncrDecr",_), 
                [ 
                    id_node,
                    itree(inode("++",_), [] )
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val inc = Integer(toInt(v) + 1)
          val m1 = updateStore(loc, inc, m0)
        in
          (v, m1)
        end
        
  | E(  itree(inode("IncrDecr",_), 
                [ 
                    id_node,
                    itree(inode("--",_), [] )
                ] 
             ), 
        m0
    ) = let
          val id = getLeaf(id_node)
          val loc = getLoc(accessEnv(id, m0))
          val v = accessStore(loc, m0)
          val dec = Integer(toInt(v) - 1)
          val m1 = updateStore(loc, dec, m0)
        in
          (v, m1)
        end
    
  | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  
  | E _ = raise Fail("error in Semantics.E - this should never occur")




(* Model Functions *)
fun M(  itree(inode("prog",_), 
                [ 
                    StmtList
                ] 
             ), 
        m
    ) = M( StmtList, m )
    
  (* Statement List *)
  | M( itree(inode("StmtList",_),
                [
                    Stmt,
                    itree(inode(";",_), [] ),
                    StmtList
                ]
            ),
        m0
    ) = let
          val m1 = M(Stmt, m0)
          val m2 = M(StmtList, m1)
        in
          m2
        end

  | M( itree(inode("StmtList",_),
                [
                    Stmt,
                    itree(inode(";",_), [] )
                ]
            ),
        m
    ) = M( Stmt, m )
   
  (* Statement *)
  | M( itree(inode("Stmt",_),
                [
                    Stmt
                ]
            ),
        m
    ) = M(Stmt, m)
  
  (* Declare *)
  | M( itree(inode("Declare",_),
                [
                    itree(inode("int",_), [] ),
                    id_node
                ]
            ),
        (env, n, s)
    ) = let
          val id = getLeaf(id_node)
        in
            updateEnv(id, INT, n, (env, n, s))
        end
    
  | M( itree(inode("Declare",_),
                [
                    itree(inode("bool",_), [] ),
                    id_node
                ]
            ),
        (env, n, s)
    ) = let
          val id = getLeaf(id_node)
        in
            updateEnv(id, BOOL, n, (env, n, s))
        end
   
  (* Assign *)
  | M( itree(inode("Assign",_),
                [
                    IncrDecr
                ]
            ),
        m0
    ) = let
            val (_, m1) = E(IncrDecr, m0)
        in
          m1
        end
    
  | M( itree(inode("Assign",_),
                [
                    itree(inode("bool",_), [] ),
                    id_node,
                    itree(inode("=",_), [] ),
                    Express
                ]
            ),
        m0
    ) = let
          val id = getLeaf(id_node)
          val (v, m1) = E(Express, m0)
          val (_,n,_) = m1
          val m2 = updateEnv(id, BOOL, n, m1)
          val loc = getLoc(accessEnv(id, m2))
          val m3 = updateStore(loc, v, m2)
        in
          m3
        end
    
  | M( itree(inode("Assign",_),
                [
                    itree(inode("int",_), [] ),
                    id_node,
                    itree(inode("=",_), [] ),
                    Express
                ]
            ),
        m0
    ) = let
          val id = getLeaf(id_node)
          val (v, m1) = E(Express, m0)
          val (_,n,_) = m1
          val m2 = updateEnv(id, INT, n, m1)
          val loc = getLoc(accessEnv(id, m2))
          val m3 = updateStore(loc, v, m2)
        in
          m3
        end
   
  | M( itree(inode("Assign",_),
                [
                    id_node,
                    itree(inode("=",_), [] ),
                    Express
                ]
            ),
        m0
    ) = let
          val id = getLeaf(id_node)
          val (v, m1) = E(Express, m0)
          val loc = getLoc(accessEnv(id, m1))
          val m2 = updateStore(loc, v, m1)
        in
          m2
        end
        
  (* Print *)
  | M( itree(inode("Print", _),
                [
                    itree(inode("print",_), []),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] )
                ]
            ),
            m0
     ) = let
            val (v, m1) = E(Express, m0)
            val str = varToString(v)
         in
            (print(str ^ "\n"); m1)
         end
         
  (* Cond *)
  | M( itree(inode("Cond",_),
                   [
                       Cond
                   ]
               ),
           m
       ) = M(Cond, m)

  (* If *)
  | M( itree(inode("If", _),
                [
                    itree(inode("if",_), [] ),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] ),
                    itree(inode("then",_), []),
                    Block
                ]
             ),
            m0
      ) = let
               val (v, m1) = E(Express, m0)
           in
                if toBool(v) then M(Block, m1)
                else m1
           end

  (* If Else *)
  | M( itree(inode("IfElse", _),
                  [
                    itree(inode("if",_), [] ),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] ),
                    itree(inode("then",_), []),
                    Block1,
                    itree(inode("else",_), []),
                    Block2
                  ]
               ),
              m0
        ) = let
                 val (v, m1) = E(Express, m0)
             in
                  if toBool(v) then M( Block1, m1)
                  else M(Block2, m1)
             end
  
  (* Block *)
  | M( itree(inode("Block", _),
                [
                    itree(inode("{",_), []),
                    StmtList,
                    itree(inode("}",_), [])
                ]
            ),
           (env0, n0, s0)
      ) = let
            val (_, n1, s1) = M(StmtList, (env0, n0, s0))
            val m = (env0, n1, s1)
          in
            m
          end
          
  (* Iter *)
  | M( itree(inode("Iter",_),
                [
                    Iter
                ]
            ),
        m
    ) = M(Iter, m)
  
  (* For Iter *)
  | M( itree(inode("ForIter",_),
                [
                    itree(inode("for",_), [] ),
                    itree(inode("(",_), [] ),
                    Assign1,
                    itree(inode(",",_), [] ),
                    Express,
                    itree(inode(",",_), [] ),
                    Assign2,
                    itree(inode(")",_), [] ),
                    Block
                ]
            ),
        m0
    ) = let
          val m1 = M(Assign1, m0)
          
          fun aux(m2) = 
            let
                val (v, m3) = E(Express, m2)
            in
                if toBool(v) then
                    let
                        val m4 = M(Block, m3)
                        val m5 = M(Assign2, m4)
                        val m6 = aux(m5)
                    in
                        m6
                    end
                else m3
            end
            
        in
          aux(m1)
        end

  (* While Iter *)
  | M( itree(inode("WhileIter",_),
                [
                    itree(inode("while",_), [] ),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] ),
                    Block
                ]
            ),
        m0
    ) = let
    
          fun aux(m1) = 
            let
                val (v, m2) = E(Express, m1)
            in
                if toBool(v) then
                    let
                        val m3 = M(Block, m2)
                        val m4 = aux(m3)
                    in
                        m4
                    end
                else m2
            end
            
        in
          aux(m0)
        end

  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")


(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








