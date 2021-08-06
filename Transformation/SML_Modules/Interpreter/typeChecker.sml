(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
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
            
    | typeCheck (itree(inode("StmtList",_),
                    [
                        Stmt,
                        itree(inode(";",_), [] )
                    ]
                ),
            m
        ) = typeCheck(Stmt, m)
  
   | typeCheck (itree(inode("Stmt",_),
                    [
                       Stmt
                   ]
               ),
           m
       ) = typeCheck(Stmt, m)
  
  
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








