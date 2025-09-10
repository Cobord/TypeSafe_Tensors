module Data.Container.Morphism.Instances

import Data.Fin

import Data.Container.Object.Instances
import Data.Container.Morphism.Definition
import Data.Container.Extension.Definition

import Misc

||| Ext is a functor of type Cont -> [Type, Type]
||| On objects it maps a container to a polynomial functor
||| On morphisms it maps a dependent lens to a natural transformation
public export
extMap : {c, d : Cont} ->
  c =%> d ->
  Ext c a -> Ext d a
extMap (fwd <%! bwd) (sh <| index) = fwd sh <| index . bwd sh
  

-- need to organise this
namespace BinTree
  public export
  inorderBackward : (b : BinTreeShape) ->
    Fin (numNodesAndLeaves b) ->
    BinTreePos b
  inorderBackward LeafS FZ = AtLeaf
  inorderBackward (NodeS lt rt) n with (strengthenN {m=numNodesAndLeaves lt} n)
     _ | Left p = GoLeft (inorderBackward lt p)
     _ | Right FZ = AtNode
     _ | Right (FS g) = GoRight (inorderBackward rt g)


  public export
  inorder : BinTree =%> List
  inorder = !% \b => (numNodesAndLeaves b ** inorderBackward b)

namespace BinTreeNode
  public export
  inorderBackward : (b : BinTreeShape) ->
    Fin (numNodes b) ->
    BinTreePosNode b
  inorderBackward (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
    _ | Left p = GoLeft (inorderBackward lt p)
    _ | Right FZ = AtNode
    _ | Right (FS g) = GoRight (inorderBackward rt g)

  ||| Traverses a binary tree container in order, producing a list container
  public export
  inorder : BinTreeNode =%> List
  inorder = !% \b => (numNodes b ** inorderBackward b)



  -- TODO reshape commented out for the same reason as reshapeTensorA is
  -- public export
  -- reshape : {oldShape, newShape : List Nat} ->
  --   Tensor oldShape a ->
  --   {auto prf : prod oldShape = prod newShape} ->
  --   Tensor newShape a




-- Need to do some rewriting for preorder
public export
preorderBinTreeNode : (b : BinTreeShape) -> Fin (numNodes b) -> BinTreePosNode b
preorderBinTreeNode (NodeS lt rt) x = ?preorderBinTreeNode_rhs_1
--preorderBinTreeNode (NodeS lt rt) n with (strengthenN {m=numNodes lt} n)
--  _ | Left p = ?whl
--  _ | Right FZ = ?whn
--  _ | Right (FS g) = ?whr


public export
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