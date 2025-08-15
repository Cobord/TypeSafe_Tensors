module Data.Container.Morphism.Instances

import Data.Fin

import Data.Container.Definition
import Data.Container.Applicative
import Data.Container.Morphism.Definition
import Data.Container.Instances
import Data.Container.TreeUtils
import Misc

-- Need to do some rewriting for preorder
public export
preorderBinTreeNode : (b : BinTreeShape) -> Fin (numNodes b) -> BinTreePosNode b
preorderBinTreeNode (NodeS lt rt) x = ?preorderBinTreeNode_rhs_1
--preorderBinTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
--  _ | Left p = ?whl
--  _ | Right FZ = ?whn
--  _ | Right (FS g) = ?whr

public export
inorderBinTreeNodeBw : (b : BinTreeShape) -> Fin (numNodes b) -> BinTreePosNode b
inorderBinTreeNodeBw (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
  _ | Left p = GoLeft (inorderBinTreeNodeBw lt p)
  _ | Right FZ = Done
  _ | Right (FS g) = GoRight (inorderBinTreeNodeBw rt g)
  

||| Traverses a binary tree container in order, producing a list container
public export
inorderBinTreeNode : BinTreeNode =%> List
inorderBinTreeNode = !% \b => (numNodes b ** inorderBinTreeNodeBw b)

maybeToList : Maybe =%> List
maybeToList = !% \b => case b of 
  False => (0 ** absurd)
  True => (1 ** \_ => ())

reshapeVectIndexes : (Vect n >< Vect m) =%> Vect (n * m)
reshapeVectIndexes = (\_ => ()) <%! (\((), ()) => ?reshapeVects_rhs2)

reshapeVects :
  (Vect n >< Vect m) `fullOf` a -> 
  Vect (n * m) `fullOf` a
reshapeVects (((), ()) <| indexCont)
  = () <| ?reshapeVects_rhs_4


-- public export
-- traverseLeaf : (x : BinTreeShape) -> FinBinTreeLeaf x -> Fin (numLeaves x)
-- traverseLeaf LeafS Done = FZ
-- traverseLeaf (NodeS lt rt) (GoLeft x) = weakenN (numLeaves rt) (traverseLeaf lt x)
-- traverseLeaf (NodeS lt rt) (GoRight x) = shift (numLeaves lt) (traverseLeaf rt x)
-- 

-- reshapings are isomorphisms

{-
[3,4]        [12]
 |
 v
 a

 -}








