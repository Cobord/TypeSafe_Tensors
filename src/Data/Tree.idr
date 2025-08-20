module Data.Tree

import Language.Reflection
import Derive.Prelude
import Misc

%language ElabReflection

{-----------------------------------------------------------
{-----------------------------------------------------------
This file contains definitions of many useful tree types.
These definitions are all inductive, representing finite
trees, and generally used as concrete representations of
tree containers.

-----------------------------------------------------------}
-----------------------------------------------------------}

namespace BinaryTrees
  ||| Finite binary trees with labels on leaves and nodes
  public export
  data BinTree : (leafType : Type) -> (nodeType : Type) -> Type where
      Leaf : leafType -> -- leaf value
        BinTree leafType nodeType
      Node : nodeType -> -- node value
        BinTree leafType nodeType -> -- left subtree
        BinTree leafType nodeType -> -- right subtree
        BinTree leafType nodeType

  %runElab derive "BinTree" [Eq, Show]
  %name BinTree bt, bt', bt''

  public export
  Bifunctor BinTree where
      bimap f g (Leaf x) = Leaf (f x)
      bimap f g (Node n leftTree rightTree)
        = Node (g n) (bimap f g leftTree) (bimap f g rightTree)

  -- {leafType : Type} -> Applicative (\n => BinTree leafType n) where
  -- (Leaf f) <*> (Leaf x) = Leaf (f x)
  -- (Leaf f) <*> (Node n leftTree rightTree) = Node n (f <*> leftTree) (f <*> rightTree)
  -- (Node n leftTree rightTree) <*> (Leaf x) = Node n (leftTree <*> (Leaf x)) (rightTree <*> (Leaf x))
  -- (Node n leftTree rightTree) <*> (Node m v s) = Node n (leftTree <*> v) (rightTree <*> s)

  namespace BinTreeSame
    ||| Binary trees with the same type of value on both leaves and nodes
    public export
    BinTreeSame : (content : Type) -> Type
    BinTreeSame content = BinTree content content

    public export
    Functor BinTreeSame where
      map f (Leaf x) = Leaf (f x)
      map f (Node x leftTree rightTree) = Node (f x)
        (map {f=BinTreeSame} f leftTree)
        (map {f=BinTreeSame} f rightTree)


    ||| Smaller tree expands to the shape of a bigger one
    ||| We can do this for BinTreeSame but not for BinTree precisely
    ||| because we copy the leaf value across to the nodes
    public export
    liftA2BinTreeSame : BinTreeSame a -> BinTreeSame b -> BinTreeSame (a, b)
    liftA2BinTreeSame (Leaf a) (Leaf b) = Leaf (a, b)
    liftA2BinTreeSame l@(Leaf a) (Node b ltb rtb)
      = Node (a, b) (liftA2BinTreeSame l ltb) (liftA2BinTreeSame l rtb)
    liftA2BinTreeSame (Node a lta rta) l@(Leaf b)
      = Node (a, b) (liftA2BinTreeSame lta l) (liftA2BinTreeSame rta l)
    liftA2BinTreeSame (Node a lta rta) (Node b ltb rtb)
      = Node (a, b) (liftA2BinTreeSame lta ltb) (liftA2BinTreeSame rta rtb)


    public export
    Applicative BinTreeSame where
      {-
      Maps a single value to a Leaf node with that value
      We can technically create an arbitrary tree with this, but 
      it's not clear whether any one except Leaf is canonical
      -}
      pure a = Leaf a
      fs <*> xs = map {f=BinTreeSame} (uncurry ($)) $ liftA2BinTreeSame fs xs
  
  

  namespace LeavesOnly
    public export
    BinTreeLeaf : (leafType : Type) -> Type
    BinTreeLeaf leafType = BinTree leafType ()

    ||| Helper function to construct a node with a trivial value
    public export
    Node' : BinTree l () -> BinTree l () -> BinTree l ()
    Node' = Node ()
  
    public export
    Functor BinTreeLeaf where
        map f (Leaf x) = Leaf (f x)
        map f (Node x leftTree rightTree) = Node x
          (map {f=BinTreeLeaf} f leftTree)
          (map {f=BinTreeLeaf} f rightTree)
  
    public export
    liftA2BinTreeLeaf : BinTreeLeaf a -> BinTreeLeaf b -> BinTreeLeaf (a, b)
    liftA2BinTreeLeaf (Leaf a) (Leaf b)
      = Leaf (a, b)
    liftA2BinTreeLeaf l@(Leaf x) (Node n z w)
      = Node n (liftA2BinTreeLeaf l z) (liftA2BinTreeLeaf l w)
    liftA2BinTreeLeaf (Node n z w) (Leaf x)
      = Node n (liftA2BinTreeLeaf z (Leaf x)) (liftA2BinTreeLeaf w (Leaf x))
    liftA2BinTreeLeaf (Node n y z) (Node m v s)
      = Node n (liftA2BinTreeLeaf y v) (liftA2BinTreeLeaf z s) -- there's a choice here on what node to use! Maybe if we had a dot there?
  
    public export
    Applicative BinTreeLeaf where
        pure x = Leaf x
        fs <*> xs = map {f=BinTreeLeaf} (uncurry ($)) $ liftA2BinTreeLeaf fs xs 
  
    -- Is this even possible?
    -- probably is, but foldable really means traversing in a linear order
    -- with tree in principle we'd have to process each subtree in parallel
    -- but we could implement foldable by first making a choice on how to traverse a tree and turn it into a list, and then performing the fold on the resulting list
    public export
    Foldable BinTreeLeaf where
      foldr f z (Leaf leaf) = f leaf z
      foldr f z (Node _ leftTree rightTree) = ?oo_1 where
        leftTreeRes : acc
        leftTreeRes = foldr {t=BinTreeLeaf} f z leftTree
        rightTreeRes = foldr {t=BinTreeLeaf} f z rightTree
  
  namespace NodesOnly
    public export
    BinTreeNode : (nodeType : Type) -> Type
    BinTreeNode nodeType = BinTree () nodeType

    ||| Helper function to construct a leaf with a trivial value
    public export
    Leaf' : BinTree () n
    Leaf' = Leaf ()
  
    public export
    Functor BinTreeNode where
      map f (Leaf leaf) = Leaf leaf -- only one element
      map f (Node node leftTree rightTree)
        = Node (f node) (map {f=BinTreeNode} f leftTree) (map {f=BinTreeNode} f rightTree) 
  
    -- Does this work only when the shapes match fully?
    public export
    liftA2BinTreeNode : BinTreeNode n -> BinTreeNode m -> BinTreeNode (n, m)
    liftA2BinTreeNode (Node n lt rt) (Node m lt' rt') = Node (n, m) (liftA2BinTreeNode lt lt') (liftA2BinTreeNode rt rt')
    liftA2BinTreeNode _ _ = Leaf ()
  
    public export
    Applicative BinTreeNode where
      pure a = Leaf () -- Is this correct?
      fs <*> xs = map {f=BinTreeNode} (uncurry ($)) $ liftA2BinTreeNode fs xs 

  
  namespace Traversals
    {- 
         4
        / \
       2   5
      /\
     1  3
    
     -}
    t : BinTree Int Int
    t = Node 4 (Node 2 (Leaf 1) (Leaf 3)) (Leaf 5)
  
    public export
    inorder : BinTree a b -> List (Either a b)
    inorder (Leaf leaf) = [Left leaf]
    inorder (Node node leftTree rightTree) =
      inorder leftTree ++ [Right node] ++ inorder rightTree
  
    testInorder :
      Traversals.inorder Traversals.t = [Left 1, Right 2, Left 3, Right 4, Left 5]
    testInorder = Refl
  
    public export
    preorder : BinTree a b -> List (Either a b)
    preorder (Leaf leaf) = [Left leaf]
    preorder (Node node leftTree rightTree) =
      [Right node] ++ preorder leftTree ++ preorder rightTree
  
    testPreorder : Traversals.preorder Traversals.t
      = [Right 4, Right 2, Left 1, Left 3, Left 5]
    testPreorder = Refl
  
    public export
    postorder : BinTree a b -> List (Either a b)
    postorder (Leaf leaf) = [Left leaf]
    postorder (Node node leftTree rightTree)
      = postorder leftTree ++ postorder rightTree ++ [Right node]
  
    testPostorder : Traversals.postorder Traversals.t
      = [Left 1, Left 3, Right 2, Left 5, Right 4]
    testPostorder = Refl
  
    public export
    fromEitherUnit : List (Either a ()) -> List a
    fromEitherUnit [] = []
    fromEitherUnit ((Left a) :: xs) = a :: fromEitherUnit xs
    fromEitherUnit ((Right ()) :: xs) = fromEitherUnit xs
  
    public export
    fromUnitEither : List (Either () a) -> List a
    fromUnitEither [] = []
    fromUnitEither ((Right a) :: xs) = a :: fromUnitEither xs
    fromUnitEither ((Left ()) :: xs) = fromUnitEither xs
  
    ||| For leaf-only trees, inorder=preorder=postorder
    public export
    traverseBinTreeLeaf : BinTreeLeaf a -> List a
    traverseBinTreeLeaf bt = fromEitherUnit (inorder bt)
  
  
    public export
    inorderNode : BinTreeNode a -> List a
    inorderNode bt = fromUnitEither (inorder bt)
  
    public export
    preorderNode : BinTreeNode a -> List a
    preorderNode bt = fromUnitEither (preorder bt)
  
    public export
    postorderNode : BinTreeNode a -> List a
    postorderNode bt = fromUnitEither (postorder bt)



namespace RoseTrees
  ||| This can likely be generalised to work for an arbitrary applicative
  ||| instead of just List
  public export
  data RoseTree : (leafType : Type) -> (nodeType : Type) -> Type where
    Leaf : leafType -> -- leaf value
      RoseTree leafType nodeType
    Node : nodeType -> -- node value
      List (RoseTree leafType nodeType) -> -- list of children
      RoseTree leafType nodeType

  %runElab derive "RoseTree" [Eq, Show]
  %name RoseTree rt, rt', rt''


  namespace RoseTreeSame
    public export
    RoseTreeSame : (content : Type) -> Type
    RoseTreeSame content = RoseTree content content

    public export
    Functor RoseTreeSame where
      map f (Leaf x) = Leaf (f x)
      map f (Node x subTrees) = Node (f x) (map {f=RoseTreeSame} f <$> subTrees)

    public export
    liftA2RoseTreeSame : RoseTreeSame a -> RoseTreeSame b -> RoseTreeSame (a, b)
    liftA2RoseTreeSame (Leaf a) (Leaf b) = Leaf (a, b)
    liftA2RoseTreeSame l@(Leaf a) (Node b subTreesb)
      = Node (a, b) ((\st => liftA2RoseTreeSame l st) <$> subTreesb)
    liftA2RoseTreeSame (Node a subTreesa) l@(Leaf b)
      = Node (a, b) ((\st => liftA2RoseTreeSame st l) <$> subTreesa)
    -- For this last case we need to use a particular applicative structure of List! 
    liftA2RoseTreeSame (Node a subTreesa) (Node b subTreesb)
      = Node (a, b) ((uncurry liftA2RoseTreeSame) <$> (listZip subTreesa subTreesb))

    ||| Making RoseTreeSame an applicative relies on the applicative structure of lists
    public export
    Applicative RoseTreeSame where
      pure a = Leaf a
      fs <*> xs = map {f=RoseTreeSame} (uncurry ($)) $ liftA2RoseTreeSame fs xs


    public export
    {a : Type} -> Display a => Display (RoseTreeSame a) where
      display (Leaf x) = display x
      display (Node x rts)
        = let (xh ** xw ** dx) = display x 
          in ?whatt_1

  -- Idris' totality checker does not accept this as total
  -- public export
  -- Bifunctor RoseTree where
  --   bimap f g (Leaf a) = Leaf (f a)
  --   bimap f g (Node b subTrees) = Node (g b) (bimap f g <$> subTrees)


--   public export
--   Foldable (RoseTree leafType) where
--     foldr f z (Leaf x) = f x z
--     foldr f z (Node n children) = foldr {f=RoseTree leafType} f (foldr {f=RoseTree leafType} f z children) n
-- 
  
  

namespace TreeRotation
  -- not really used, works for binary trees
  {-
  Can only rotate right trees of the shape
  
     /\
    /\ c
   a b
  
  Other shapes, such as
  
    a
  
  
    or
  
    /\
    a b
  
  
     or
  
     /\
    a /\   --- here a could be a Leaf node, making this equal to the case above
      b c
  
  don't work
  -}
  public export
  data CanRotateRight : (BinTree : BinTreeLeaf a) -> Type where
    RotateRight : (leftLeftTree : BinTreeLeaf a)
               -> (leftRightTree : BinTreeLeaf a)
               -> (rightTree : BinTreeLeaf a)
               -> CanRotateRight (Node' (Node' leftLeftTree leftRightTree) rightTree)
  
  
  --  public export
  --  cannotRotateLeaf : CanRotateRight (Leaf leaf) -> Void
  --  cannotRotateLeaf (RotateRight _ _ _) impossible
  
  --  public export
  --   cannotRotateThisTree : CanRotateRight (Node n (Leaf l) (Node n' lt rt)) -> Void
  --   cannotRotateThisTree (RotateRight _ _ _) impossible
  
  {-
  
     /\             /\   
    /\ c    -->    a /\
   a b               b c
  
  -}
  -- Tree rotation
  public export
  rotateRight : (tree : BinTreeLeaf a)
             -> (CanRotateRight tree)
             -> BinTreeLeaf a
  rotateRight (Node n (Node n' leftLeftTree leftRightTree) rightTree) x
    = Node n leftLeftTree (Node n' leftRightTree rightTree)
  
  
  
  
  
  PathBinTree : Type
  PathBinTree = List Bool
  
  
  -- Swap the left and right subtrees at at specified path
  commute : PathBinTree -> BinTreeLeaf l -> BinTreeLeaf l
  commute [] (Leaf leaf) = Leaf leaf
  commute [] (Node node l r) = Node node r l
  commute (x :: xs) (Leaf leaf) = Leaf leaf
  commute (False :: xs) (Node node l r) = Node node (commute xs l) r
  commute (True :: xs) (Node node l r) = Node node l (commute xs r)



