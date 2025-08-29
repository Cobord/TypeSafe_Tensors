module Data.Container.Morphism.Instances

import Data.Fin

import Data.Container.Object.Instances
import Data.Container.Morphism.Definition
import Data.Container.Extension.Definition

import Misc

-- need to organise this

||| Ext is a functor of type Cont -> [Type, Type]
||| On objects it maps a container to a polynomial functor
||| On morphisms it maps a dependent lens to a natural transformation
||| Can be used to reshape tensors, among others
public export
restructure : {c1, c2 : Cont} ->
  (c1 =%> c2) ->
  Ext c1 a -> Ext c2 a
restructure (fwd <%! bwd) (sh <| index) = fwd sh <| (\y' => index (bwd sh y'))




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
reshapeVects (((), ()) <| index)
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








