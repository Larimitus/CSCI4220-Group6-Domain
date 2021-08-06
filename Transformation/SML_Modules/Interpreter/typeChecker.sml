(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expressession notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

exception model_error;


fun typeOf( itree(inode("Express",_),
                [
                    Express,
                    itree(inode("or",_), [] ),
                    LogicAnd
                ]
            ),
        m
    ) = let
          val t1 = typeOf( Express, m )
          val t2 = typeOf( LogicAnd, m )
        in
          if t1 = t2 andalso t1 = BOOL then BOOL
          else ERROR
        end
    | typeOf( itree(inode("Express",_), [ LogicEqual ] ), m) = typeOf(LogicEqual, m)
    
(* LogicalAnd *)
| typeOf( itree(inode("LogicalAnd",_),
              [
                  LogicalAnd,
                  itree(inode("and",_), [] ),
                  LogicEqual
              ]
          ),
      m
  ) = let
        val t1 = typeOf( LogicalAnd, m )
        val t2 = typeOf( LogicEqual, m )
      in
        if t1 = t2 andalso t1 = BOOL then BOOL
        else ERROR
      end

  | typeOf( itree(inode("LogicalAnd",_), [ LogicEqual ] ), m) = typeOf(LogicEqual, m)
  
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

  | typeOf( itree(inode("RelOp",_), [ AddOpp ] ), m) = typeOf(AddOpp, m)

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
  
  (* UniMin *)
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
  
  (* Exponent *)
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
                    express,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) = typeOf(express, m)

  | typeOf( itree(inode("Ops",_),
                [
                    itree(inode("|",_), [] ),
                    express,
                    itree(inode("|",_), [] )
                ]
            ),
        m
    ) = let
          val t = typeOf( express, m )
        in
          if t = INT then INT
          else ERROR
        end

  | typeOf( itree(inode("Ops",_),
                [
                    itree(inode("not",_), [] ),
                    itree(inode("(",_), [] ),
                    express,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) = let
          val t = typeOf( express, m )
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
        

fun typeCheck(itree(inode("prog",_), [ StmtList ] ), m) = typeCheck(StmtList, m)

  (* StmtList *)
  | typeCheck (itree(inode("StmtList",_),
                    [
                        Stmt,
                        itree(inode(";",_), [] ),
                        StmtList
                    ]
                ),
            m0
        ) = 
            let
                val m1 = typeCheck(Stmt, m0)
                val m2 = typeCheck(StmtList, m1)
            in
                m2
            end
    (* StmtList *)        
    | typeCheck (itree(inode("StmtList",_),
                    [
                        Stmt,
                        itree(inode(";",_), [] )
                    ]
                ),
            m
        ) = typeCheck(Stmt, m)
       
  (* Stmt *)
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
  (* Declare *)  
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
  (* Assign *)  
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
  (* Assign *)  
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
  (* Assign *)
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
   
  (* Print *) 
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
  
  (* If *)
  | typeCheck(itree(inode("If", _),
                    [
                    itree(inode("if",_), [] ),
                    itree(inode("(",_), [] ),
                    Express,
                    itree(inode(")",_), [] ),
                    itree(inode("then",_), []),
                    block1
                    ]
                 ),
              m
           ) = let
                  val t1 = typeOf( Express, m )
                  val m1 = typeCheck( block1, m )
               in
                  if t1 = BOOL then m
                  else raise model_error
               end
               
  (* IfElse *)
  | typeCheck(itree(inode("IfElse", _),
                  [
                      itree(inode("if",_), [] ),
                      itree(inode("(",_), [] ),
                      Express,
                      itree(inode(")",_), [] ),
                      itree(inode("then",_), []),
                      block1,
                      itree(inode("else",_), []),
                      block2
                  ]
               ),
              m
          ) = let
                  val t1 = typeOf( Express, m )
                  val m1 = typeCheck( block1, m )
                  val m2 = typeCheck( block2, m )
              in
                 if t1 = BOOL then m
                 else raise model_error
              end
  (* Block *)            
  | typeCheck(itree(inode("Block",_), 
                [
                    itree(inode("{",_), []),
                    stmtList,
                    itree(inode("}",_), [])
                ]
            ),
          m0
      ) = let
            val m1 = typeCheck( stmtList, m0 )
          in
            m0
          end
   (* Iter *)
   | typeCheck(itree(inode("Iter",_),
                    [
                        Iter
                    ]
            ),
          m
        ) = typeCheck(Iter, m)
   (* ForIter *)
   | typeCheck (itree(inode("ForIter",_),
                [
                  itree(inode("for",_), [] ),
                  itree(inode("(",_), [] ),
                  assignment1,
                  itree(inode(",",_), [] ),
                  Express,
                  itree(inode(",",_), [] ),
                  assignment2,
                  itree(inode(")",_), [] ),
                  Block
                ]
            ),
         m0
        ) = let
                val m1 = typeCheck( assignment1, m0 )
                val t1 = typeOf( Express, m1 )
                val m2 = typeCheck( Block, m1 )
                val m3 = typeCheck( assignment2, m2 )
            in
                if t1 = BOOL then m0
                else raise model_error
            end
  (* WhileIter *)          
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








