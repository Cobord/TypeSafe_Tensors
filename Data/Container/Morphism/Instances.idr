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
preorderBTreeNode : (b : BTreeShape) -> Fin (numNodes b) -> FinBTreeNode b
preorderBTreeNode (NodeS lt rt) x = ?preorderBTreeNode_rhs_1
--preorderBTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
--  _ | Left p = ?whl
--  _ | Right FZ = ?whn
--  _ | Right (FS g) = ?whr

public export
inorderBTreeNode : (b : BTreeShape) -> Fin (numNodes b) -> FinBTreeNode b
inorderBTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
  _ | Left p = GoLeft (inorderBTreeNode lt p)
  _ | Right FZ = Done
  _ | Right (FS g) = GoRight (inorderBTreeNode rt g)
  

||| Converts a container of a binary tree with data stored at leaves to 
||| a list container
public export
bTreeNodePreorder : BTreeNode =%> List
bTreeNodePreorder = !% \b => (numNodes b ** inorderBTreeNode b)

boolToNat : Bool -> Nat
boolToNat False = 0
boolToNat True = 1

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
-- traverseLeaf : (x : BTreeShape) -> FinBTreeLeaf x -> Fin (numLeaves x)
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








