(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    Expressession notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

exception model_error;


fun typeOf( itree(inode("Express",_), [ LogicOr ] ), m) = typeOf(LogicOr, m)

  (* Logical Or *)
  | typeOf( itree(inode("LogicOr",_),
                [
                    LogicOr,
                    itree(inode("||",_), [] ),
                    LogicAnd
                ]
            ),
        m
    ) = let
          val t1 = typeOf( LogicOr, m )
          val t2 = typeOf( LogicAnd, m )
        in
          if t1 = t2 andalso t1 = BOOL then BOOL
          else ERROR
        end

  | typeOf( itree(inode("LogicOr",_), [ LogicAnd ] ), m) = typeOf(LogicAnd, m)

  (* Logical And *)
  | typeOf( itree(inode("LogicAnd",_),
                [
                    LogicAnd,
                    itree(inode("&&",_), [] ),
                    LogicEqual
                ]
            ),
        m
    ) = let
          val t1 = typeOf( LogicAnd, m )
          val t2 = typeOf( LogicEqual, m )
        in
          if t1 = t2 andalso t1 = BOOL then BOOL
          else ERROR
        end

  | typeOf( itree(inode("LogicAnd",_), [ LogicEqual ] ), m) = typeOf(LogicEqual, m)

  (* LogicEqual *)
  | typeOf( itree(inode("LogicEqual",_),
                [
                    LogicEqual,
                    itree(inode("==",_), [] ),
                    RelOp
                ]
            ),
        m
    ) = let
          val t1     = typeOf( LogicEqual, m )
          val t2     = typeOf( RelOp, m )
        in
          if t1 = t2 andalso t1 <> ERROR then BOOL
          else ERROR
        end
        
  | typeOf( itree(inode("LogicEqual",_),
                [
                    LogicEqual,
                    itree(inode("!=",_), [] ),
                    RelOp
                ]
            ),
        m
    ) = let
          val t1 = typeOf( LogicEqual, m )
          val t2 = typeOf( RelOp, m )
        in
          if t1 = t2 andalso t1 <> ERROR then BOOL
          else ERROR
        end

  | typeOf( itree(inode("LogicEqual",_), [ RelOp ] ), m) = typeOf(RelOp, m)

  (* RelOp *)
  | typeOf( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode("<",_), [] ),
                    AddOp2
                ]
            ),
        m
    ) = let
          val t1 = typeOf( AddOp1, m )
          val t2 = typeOf( AddOp2, m )
        in
          if t1 = t2 andalso t1 = INT then BOOL
          else ERROR
        end

  | typeOf( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode("<=",_), [] ),
                    AddOp2
                ]
            ),
        m
    ) = let
          val t1 = typeOf( AddOp1, m )
          val t2 = typeOf( AddOp2, m )
        in
          if t1 = t2 andalso t1 = INT then BOOL
          else ERROR
        end

  | typeOf( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode(">",_), [] ),
                    AddOp2
                ]
            ),
        m
    ) = let
          val t1 = typeOf( AddOp1, m )
          val t2 = typeOf( AddOp2, m )
        in
          if t1 = t2 andalso t1 = INT then BOOL
          else ERROR
        end

  | typeOf( itree(inode("RelOp",_),
                [
                    AddOp1,
                    itree(inode(">=",_), [] ),
                    AddOp2
                ]
            ),
        m
    ) = let
          val t1 = typeOf( AddOp1, m )
          val t2 = typeOf( AddOp2, m )
        in
          if t1 = t2 andalso t1 = INT then BOOL
          else ERROR
        end

  | typeOf( itree(inode("RelOp",_), [ AddOp ] ), m) = typeOf(AddOp, m)

  (* AddOp *)
  | typeOf( itree(inode("AddOp",_),
                [
                    AddOp,
                    itree(inode("+",_), [] ),
                    MultiOp
                ]
            ),
        m
    ) = let
          val t1 = typeOf( AddOp, m )
          val t2 = typeOf( MultiOp, m )
        in
          if t1 = t2 andalso t1 = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("AddOp",_),
                [
                    AddOp,
                    itree(inode("-",_), [] ),
                    MultiOp
                ]
            ),
        m
    ) = let
          val t1 = typeOf( AddOp, m )
          val t2 = typeOf( MultiOp, m )
        in
          if t1 = t2 andalso t1 = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("AddOp",_), [ MultiOp ] ), m) = typeOf(MultiOp, m)
  
  (* MultiOp *)
  | typeOf( itree(inode("MultiOp",_),
                [
                    MultiOp,
                    itree(inode("*",_), [] ),
                    UniMin
                ]
            ),
        m
    ) = let
          val t1 = typeOf( MultiOp, m )
          val t2 = typeOf( UniMin, m )
        in
          if t1 = t2 andalso t1 = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("MultiOp",_),
                [
                    MultiOp,
                    itree(inode("/",_), [] ),
                    UniMin
                ]
            ),
        m
    ) = let
          val t1 = typeOf( MultiOp, m )
          val t2 = typeOf( UniMin, m )
        in
          if t1 = t2 andalso t1 = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("MultiOp",_),
                [
                    MultiOp,
                    itree(inode("%",_), [] ),
                    UniMin
                ]
            ),
        m
    ) = let
          val t1 = typeOf( MultiOp, m )
          val t2 = typeOf( UniMin, m )
        in
          if t1 = t2 andalso t1 = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("MultiOp",_), [ UniMin ] ), m) = typeOf(UniMin, m)

  (* Unary Minus *)
  | typeOf( itree(inode("UniMin",_),
                [
                    itree(inode("-",_), [] ),
                    UniMin
                ]
            ),
        m
    ) = let
          val t = typeOf( UniMin, m )
        in
          if t = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("UniMin",_), [ ExpOp ] ), m) = typeOf(ExpOp, m)
  
  (* ExpOp *)
  | typeOf( itree(inode("ExpOp",_),
                [
                    Ops,
                    itree(inode("^",_), [] ),
                    ExpOp
                ]
            ),
        m
    ) = let
          val t1 = typeOf( Ops, m )
          val t2 = typeOf( ExpOp, m )
        in
          if t1 = t2 andalso t1 = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("ExpOp",_), [ Ops ] ), m) = typeOf(Ops, m)
  
  (* Ops *)
  | typeOf( itree(inode("Ops",_),
                [
                    operation
                ]
            ),
        m
    ) = typeOf(operation, m)

  | typeOf( itree(inode("Ops",_),
                [
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) = typeOf(Express, m)

  | typeOf( itree(inode("Ops",_),
                [
                    itree(inode("|",_), [] ),
                    Express,
                    itree(inode("|",_), [] )
                ]
            ),
        m
    ) = let
          val t = typeOf( Express, m )
        in
          if t = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("Ops",_),
                [
                    itree(inode("not",_), [] ),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) = let
          val t = typeOf( Express, m )
        in
          if t = BOOL then BOOL
          else ERROR
        end
  
  (* Identifier *)
  | typeOf( itree(inode("identifier",_),
                [
                    id_node
                ]
            ),
        m
    ) = getType(accessEnv(getLeaf(id_node), m))

  (* Value *)
  | typeOf( itree(inode("Value",_),
                [
                    itree(inode("true",_), [] )
                ]
            ),
        m
    ) = BOOL
        
  | typeOf( itree(inode("Value",_),
                [
                    itree(inode("false",_), [] )
                ]
            ),
        m
    ) = BOOL

  | typeOf( itree(inode("Value",_),
                [
                    integer
                ]
            ),
        m
    ) = INT

  (* IncrDecr *)
  | typeOf( itree(inode("IncrDecr",_), 
                [ 
                    itree(inode("++",_), [] ),
                    id_node
                ] 
             ), 
        m
    ) = let
          val t = getType(accessEnv(getLeaf(id_node), m))
        in
          if t = INT then INT
          else ERROR
        end

  | typeOf(  itree(inode("IncrDecr",_), 
                [ 
                    itree(inode("--",_), [] ),
                    id_node
                ] 
             ), 
        m
   ) = let
          val t = getType(accessEnv(getLeaf(id_node), m))
        in
          if t = INT then INT
          else ERROR
        end

  | typeOf(  itree(inode("IncrDecr",_), 
                [ 
                    id_node,
                    itree(inode("++",_), [] )
                ] 
             ), 
        m
    ) = let
          val t = getType(accessEnv(getLeaf(id_node), m))
        in
          if t = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("IncrDecr",_), 
                [ 
                    id_node,
                    itree(inode("--",_), [] )
                ] 
             ), 
        m
    ) = let
          val t = getType(accessEnv(getLeaf(id_node), m))
        in
          if t = INT then INT
          else ERROR
        end
  
  | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")

  | typeOf _ = raise Fail("Error in Model.typeOf - this should never occur")


fun typeCheck( itree(inode("prog",_), [ StmtList ] ), m) = typeCheck(StmtList, m)

  (* Statement List *)
  | typeCheck( itree(inode("StmtList",_),
                        [
                            Stmt,
                            itree(inode(";",_), [] ),
                            StmtList
                        ]
                    ),
                m0
            ) = let
                  val m1 = typeCheck(Stmt, m0)
                  val m2 = typeCheck(StmtList, m1)
                in
                  m2
                end
                
    | typeCheck( itree(inode("StmtList",_),
                        [
                            Stmt,
                            itree(inode(";",_), [] )
                        ]
                    ),
                m
            ) = typeCheck(Stmt, m)
            
  (* Statement *)
  | typeCheck( itree(inode("Stmt",_),
                [
                    Stmt
                ]
            ),
        m
    ) = typeCheck(Stmt, m)
  
  (* Declare *)
  | typeCheck( itree(inode("Declare",_),
                [
                    itree(inode("int",_), [] ),
                    id_node
                ]
            ),
        m
    ) = let
          val id = getLeaf(id_node)
          val (_,n,_) = m
        in
            updateEnv(id, INT, n, m)
        end
    
  | typeCheck( itree(inode("Declare",_),
                [
                    itree(inode("bool",_), [] ),
                    id_node
                ]
            ),
        m
    ) = let
          val id = getLeaf(id_node)
          val (_,n,_) = m
        in
            updateEnv(id, BOOL, n, m)
        end
  
  (* Assign *)
  | typeCheck( itree(inode("Assign",_),
                [
                    IncrDecr
                ]
            ),
        m
    ) = let
            val t1 = typeOf(IncrDecr, m)
        in
          if t1 = ERROR then raise model_error
          else m
        end
    
  | typeCheck( itree(inode("Assign",_),
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
          val t = typeOf(Express, m0)
          val (_,n,_) = m0
          val m1 = updateEnv(id, BOOL, n, m0)
        in
          if t = BOOL then m1
          else raise model_error
        end
    
  | typeCheck( itree(inode("Assign",_),
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
          val t = typeOf(Express, m0)
          val (_,n,_) = m0
          val m1 = updateEnv(id, INT, n, m0)
        in
          if t = INT then m1
          else raise model_error
        end
   
  | typeCheck( itree(inode("Assign",_),
                [
                    id_node,
                    itree(inode("=",_), [] ),
                    Express
                ]
            ),
        m
    ) = let
          val id = getLeaf(id_node)
          val t1 = typeOf(Express, m)
          val t2 = getType(accessEnv(id, m))
        in
          if t1 = t2 andalso t1 <> ERROR then m
          else raise model_error
        end
   
  (* print *) 
  | typeCheck(itree(inode("Print", _),
                    [
                        itree(inode("print",_), []),
                        itree(inode("(",_), [] ),
                        Express,
                        itree(inode(")",_), [] )
                    ]
                ),
                m0
        ) = let
                val t1 = typeOf( Express, m0 )
            in
                if t1 = ERROR then raise model_error
                else m0
            end
            
  (* Cond *)
  | typeCheck(itree(inode("Cond",_),
                    [
                        Cond
                    ]
                ),
            m
        ) = typeCheck(Cond, m)
  
  (* if *)
  | typeCheck(itree(inode("If", _),
                    [
                    itree(inode("if",_), [] ),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] ),
                    itree(inode("then",_), []),
                    Block1
                    ]
                 ),
              m
           ) = let
                  val t1 = typeOf( Express, m )
                  val m1 = typeCheck( Block1, m )
               in
                  if t1 = BOOL then m
                  else raise model_error
               end
               
  (* if else *)
  | typeCheck(itree(inode("IfElse", _),
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
              m
          ) = let
                  val t1 = typeOf( Express, m )
                  val m1 = typeCheck( Block1, m )
                  val m2 = typeCheck( Block2, m )
              in
                 if t1 = BOOL then m
                 else raise model_error
              end
  (* Block *)            
  | typeCheck(itree(inode("Block",_), 
                [
                    itree(inode("{",_), []),
                    StmtList,
                    itree(inode("}",_), [])
                ]
            ),
          m0
      ) = let
            val m1 = typeCheck( StmtList, m0 )
          in
            m0
          end
   
   | typeCheck(itree(inode("Iter",_),
                    [
                        Iter
                    ]
            ),
          m
        ) = typeCheck(Iter, m)
        
   | typeCheck (itree(inode("ForIter",_),
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
                val m1 = typeCheck( Assign1, m0 )
                val t1 = typeOf( Express, m1 )
                val m2 = typeCheck( Block, m1 )
                val m3 = typeCheck( Assign2, m2 )
            in
                if t1 = BOOL then m0
                else raise model_error
            end
            
  | typeCheck(itree(inode("WhileIter",_),
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
            val t1     = typeOf( Express, m0 )
            val m1     = typeCheck( Block, m0 )
        in
            if t1 = BOOL then m0
        else raise model_error
        
        end


            
            

  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








