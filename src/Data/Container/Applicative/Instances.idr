module Data.Container.Applicative.Instances

import Data.Fin
import Data.DPair

import Data.Container.Definition
import Data.Container.Instances
import Data.Container.Applicative.Definition
import Data.Tree
import Misc

%hide Prelude.(<|)


namespace ApplicativeInstances
  ||| Container with a single thing
  public export
  Scalar : ContA
  Scalar = (#) Scalar
  
  ||| Product
  public export
  Pair : ContA
  Pair = (#) Pair

  -- TODO applicatives for these commented out types?
  -- ||| Coproduct
  -- public export
  -- Either : ContA
  -- Either = (#) Either

  -- ||| +1  
  -- public export
  -- Maybe : ContA
  -- Maybe = (#) Maybe
  
  public export
  List : ContA
  List = (#) List
  
  ||| Container of n things 
  ||| Every natural number n corresponds to a Vect n, which is applicative
  ||| Used in cubical tensors whose shapes are defined by lists of natural numbers
  public export
  Vect : Nat -> ContA
  Vect n = (#) (Vect n)

  ||| Container of an infinite number of things
  public export
  Stream : ContA
  Stream = (#) Stream

  ||| Binary trees with data stored at both nodes and leaves
  public export
  BinTree : ContA
  BinTree = (#) BinTree
  
  ||| Binary trees with data stored at nodes
  public export
  BinTreeNode : ContA
  BinTreeNode = (#) BinTreeNode
  
  ||| Binary trees with data stored at leaves
  public export
  BinTreeLeaf : ContA
  BinTreeLeaf = (#) BinTreeLeaf

  public export
  RoseTree : ContA
  RoseTree = (#) RoseTree

  -- namespace ContDefs
  --   ||| Rose trees with data stored at both nodes and leaves
  --   public export
  --   RoseTree : Cont
  --   RoseTree = (t : RoseTreeShape List) !> RoseTreePos List t
  
  --   ||| Rose trees with data stored at nodes
  --   public export
  --   RoseTreeNode : Cont
  --   RoseTreeNode = (t : RoseTreeShape List) !> RoseTreePosNode List t
  
  --   ||| Rose trees with data stored at leaves
  --   public export
  --   RoseTreeLeaf : Cont
  --   RoseTreeLeaf = (t : RoseTreeShape List) !> RoseTreePosLeaf List t

  public export
  Applicative (Ext (ApplicativeRoseTree c)) where
    pure a = ?one
    fs <*> xs = ?two

  public export
  ApplicativeRoseTree : ContA -> ContA
  ApplicativeRoseTree c = (#) (ApplicativeRoseTree c)



namespace ConversionFunctions
  fromRoseTreeSameToShape : RoseTreeSame a -> RoseTreeShape List
  fromRoseTreeSameToShape (Leaf a) = LeafS
  fromRoseTreeSameToShape (Node a xs)
    = NodeS $ fromList (fromRoseTreeSameToShape <$> xs)


  public export
  fromRoseTreeSameAppl : RoseTreeSame a -> ApplicativeRoseTree' List a
  fromRoseTreeSameAppl (Leaf a) = LeafS <| \_ => a
  fromRoseTreeSameAppl (Node a rts) =
    let t = fromRoseTreeSameAppl <$> fromList rts
    in NodeS (shapeExt <$> t) <| \case
      DoneNode => a
      SubTree ps posSt =>
        let rw1 : (shapeExt t = shapeExt (shapeExt <$> t)) := sym (mapShapeExt t)
            rw2 : (shapeExt (indexCont t (rewrite sym (mapShapeExt {f=shapeExt} t) in ps)) = indexCont (shapeExt <$> t) ps) := mapIndexCont {c=List} {f=shapeExt} t ps
        in indexCont
        (indexCont t (rewrite rw1 in ps))
        (rewrite rw2 in posSt)
        -- for some reason all the explicit type annotations above are needed

  public export
  toRoseTreeSameAppl : ApplicativeRoseTree' List a -> RoseTreeSame a
  toRoseTreeSameAppl (LeafS <| contentAt) = Leaf (contentAt DoneLeaf)
  toRoseTreeSameAppl (NodeS (len <| content) <| contentAt)
    = Node (contentAt DoneNode)
           (toList $ toRoseTreeSameAppl 
                  <$> (\i => content i <| contentAt . SubTree i)
                  <$> positionsCont)
    
  -- fromRoseTreeSame (Leaf a) = LeafS <| \_ => a 
  -- fromRoseTreeSame (Node a sts)
  --   = let ges = fromList sts
  --         gg = shapeExt <$> fromList (fromRoseTreeSame <$> sts)
  --         -- tes = fromRoseTreeSame <$> sts
  --     in NodeS (shapeExt <$> fromRoseTreeSame <$> fromList sts) <| \case
  --       DoneNode => a
  --       SubTree ps ww =>
  --         let g : RoseTreeShape List := indexCont (shapeExt <$> fromRoseTreeSame <$> fromList sts) ps
  --         -- first use ps to index into ges
  --         -- then use ww to index inside the result
  --             h = indexCont (fromList sts)
  --         in indexCont ?oo ?tt

  -- fromRoseTreeSame (Leaf a) = LeafS <| \_ => a
  -- fromRoseTreeSame (Node a []) = NodeS [] <| \_ => a
  -- fromRoseTreeSame (Node a (t :: ts))
  --   = let te = fromRoseTreeSame t
  --         tes = fromRoseTreeSame <$> ts
  --     in NodeS (shapeExt <$> (te :: tes)) <| ?ffn --\case
        -- DoneNode => a
        -- Here posL => indexCont te posL
        -- There posR => ?ccc
    -- = let subTreeExtensions = fromRoseTreeSame <$> subTrees
    --   in NodeS (shapeExt <$> subTreeExtensions) <| \case
    --     DoneNode => a
    --     Here posL => ?bbb
    --     There posR => ?ccc
        -- Here posL => let t = indexCont in ?bbb
        -- There posR => ?ccc
    -- let (subTrees' <| subTreesCont) = fromRoseTreeSame subTrees
    -- in NodeS subTrees' subTreesCont <| \case
    --     DoneNode => x
    --     GoLeft posL => subTreesCont (GoLeft posL)
    --     GoRight posR => subTreesCont (GoRight posR)

  -- public export
  -- RoseTree : ContA
  -- RoseTree = (#) RoseTree

  -- ||| Rose trees with data stored at nodes
  -- public export
  -- RoseTreeNode : ContA
  -- RoseTreeNode = (#) RoseTreeNode

  -- ||| Rose trees with data stored at leaves
  -- public export
  -- RoseTreeLeaf : ContA
  -- RoseTreeLeaf = (#) RoseTreeLeaf

  -- public export
  -- InternalLens : Cont -> Cont -> Cont
  -- InternalLens c d
  --   = (f : ((x : c.shp) -> (y : d.shp ** d.pos y -> c.pos x)))
  --     !> (xx : c.shp ** d.pos (fst (f xx)))