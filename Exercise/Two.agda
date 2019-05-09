-- TOTAL MARK: 26/26 (so far)
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --irrelevant-projection #-}

module Exercise.Two where

open import Lib.Basics
open import Lib.Indexed       -- important stuff in here!
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.Monad
open import Lib.Cat.Adjunction
open import Lib.Nat

open import Exercise.One

------------------------------------------------------------------------------
-- CATEGORIES OF INDEXED OBJECTS AND ARROWS
------------------------------------------------------------------------------

-- We fix an underlying category and a set I for "index"...

module _ {Obj : Set}{Arr : Obj -> Obj -> Set}(I : Set)(C : Category Arr) where

  open Category C

  -- ... and now your job is to build a new category whose
  -- objects are I-indexed families of underlying objects, and whose
  -- arrows are index-respecting families of underlying arrows

  _-C>_ : Category {I -> Obj} \ S T -> (i : I) -> Arr (S i) (T i)
  _-C>_ = record
            { idArr = \ i -> idArr
            ; _-arr-_ = \ S T i -> (S i) -arr- (T i)
            ; idArr-arr- = \ S -> ext \ i -> idArr-arr- (S i)
            ; _-arr-idArr = \ S -> ext \ i -> (S i) -arr-idArr
            ; assoc-arr- = \ f g h -> ext \ i -> assoc-arr- (f i) (g i) (h i)
            } 
  
-- Now we give you a function f : I -> J between two index sets.

module _ {Obj : Set}{Arr : Obj -> Obj -> Set}{I J : Set}
       (f : I -> J)(C : Category Arr) where

  open Category C
  open Functor

  -- Show that you get a functor from J-indexed things to I-indexed things.

  Reindex : Functor (J -C> C) (I -C> C) (f -_)
  Reindex = record { map = \ x i -> x (f i) ; mapidArr = refl ; map-arr- = \ f₁ g -> refl }

-- MARK: 4/4

------------------------------------------------------------------------------
-- FUNCTORIALITY OF ALL
------------------------------------------------------------------------------

-- We have All in the library. Show that it is a functor from
-- element-indexed sets to list-indexed sets.

module _ where

  open Functor

  all : {I : Set}{P Q : I -> Set} ->
        [ P -:> Q ] ->
        [ All P -:> All Q ]
  all f [] [] = []
  all f (i ,- is) (p ,- ps) = (f i) p ,- all f is ps


  halpALLmapidArr : forall {I} {A : I -> Set} (is : List I)
                           (x : All A is) ->
                    all (\ i₁ x₂ -> x₂) is x == x
  halpALLmapidArr [] [] = refl
  halpALLmapidArr (x ,- is) (p ,- ps) = p ,-_ $= halpALLmapidArr is ps

  halpALLmap-arr- : forall {I} {A B C : I -> Set}
                         {f : (i : I) -> A i -> B i} {g : (i : I) -> B i -> C i}
                         (x : List I) (x₁ : All A x) ->
                  all (\ i₁ x₂ -> g i₁ (f i₁ x₂)) x x₁ == all g x (all f x x₁)
  halpALLmap-arr- [] [] = refl
  halpALLmap-arr- {f = f} {g} (x ,- is) (x1 ,- x₂) = g x ( f x x1) ,-_ $= halpALLmap-arr- is x₂

  ALL : (I : Set) -> Functor (I -C> SET) (List I -C> SET) All
  ALL I = record
    { map = \ x i x₁ -> all (\ i₁ x₂ -> x i₁ x₂) i x₁
    ; mapidArr = ext \ is -> ext \ x -> halpALLmapidArr is x
    ; map-arr- = \ f g -> ext \ x -> ext \ x1 -> halpALLmap-arr- x x1
    } 

-- MARK: 6/6

------------------------------------------------------------------------------
-- ALL BY TABULATION
------------------------------------------------------------------------------

-- The list membership relation is given by thinning from singletons.

_<-_ : {I : Set} -> I -> List I -> Set
i <- is = (i ,- []) <: is

-- If every element of a list satisfies P, you should be able to
-- collect all the Ps.

tabulate : {I : Set}{P : I -> Set}(is : List I) ->
             [ (_<- is) -:> P ] -> All P is
tabulate {I} {P} [] f = []
tabulate {I} {P} (x ,- is) f = f x (os oe) ,- tabulate is (\ i z -> f i (o' z))

module _ (I : Set) where  -- fix an element set and open handy kit
  open Category (I -C> SET)
  open Functor
  open NaturalTransformation

  -- Show that the functional presentation of "each element is P"
  -- also gives you a functor.

  AllMem : Functor (I -C> SET) (List I -C> SET) \ P is -> [ (_<- is) -:> P ]
  AllMem = record
    { map = \ x i x₁ i₁ x₂ -> x i₁ (x₁ i₁ x₂)
    ; mapidArr = refl
    ; map-arr- = \ f g -> refl
    }

-- F: It's almost as if C-c C-a wrote the above function...

  -- Prove that tabulate is natural.

  helper : forall {I} {X Y : I -> Set} (f : (i : I) -> X i -> Y i)
                (x : List I) (y : (i : I) -> i ,- [] <: x -> X i) ->
         all f x (tabulate x y) == tabulate x (\ i₁ x₂ -> f i₁ (y i₁ x₂))
  helper f [] y = refl
  helper f (x ,- x₁) y = (f x (y x (os oe))) ,-_ $= helper f x₁ \ i z -> y i (o' z)

  tabulateNT : NaturalTransformation AllMem (ALL I)
  transform tabulateNT _ = tabulate
  natural tabulateNT f = ext \ x -> ext \ y -> helper f x y

-- MARK: 8/8

------------------------------------------------------------------------------
-- 26 November 2018 -- the adventure continues
------------------------------------------------------------------------------

module _ {Obj : Set}{Arr : Obj -> Obj -> Set}{I : Set}(C : Category Arr) where
  open Category C
  open Functor

  -- Show that you can get a functor from  (I -C> C) back to C, just
  -- by picking an index.

  Point : (i : I) -> Functor (I -C> C) C \ X -> X i
  Point i = record
    { map = \ x -> x i
    ; mapidArr = refl
    ; map-arr- = \ f g -> refl
    }

module _ (I : Set) where
  open Category (I -C> SET)
  open Functor
  open NaturalTransformation

  -- Prove that the "select" function from Exercise.One is natural.

  selectNTnaturalHelp : forall {I} {is js : List I} (th : is <: js)
                             {X Y : I -> Set} (f : (i : I) -> X i -> Y i) (x : All X js) ->
                      all f is (select th x) == select th (all f js x)
  selectNTnaturalHelp (o' th) f (x ,- x₁) = selectNTnaturalHelp th f x₁
  selectNTnaturalHelp (os {x₂} th) f (x ,- x₁) = f x₂ x ,-_ $= selectNTnaturalHelp th f x₁
  selectNTnaturalHelp oz f x = refl

  selectNT : {is js : List I}(th : is <: js) ->
             NaturalTransformation
               (ALL I -Func- Point SET js)
               (ALL I -Func- Point SET is)
  transform (selectNT th) X = select th
  natural (selectNT th) f = ext (\ x -> selectNTnaturalHelp th f x)

  -- Show that tabulation fuses with selection.

  selectTabulate : {I : Set}{P : I -> Set}{is js : List I}
      (th : is <: js)(f : [ (_<- js) -:> P ]) ->
      select th (tabulate js f) == tabulate is \ i x -> f i (x -<- th)
  selectTabulate {I} {P} {is} {.(_ ,- _)} (o' th) f = selectTabulate th \ i x -> f i (o' x)
  selectTabulate {I} {P} {.(x ,- ys)} {.(x ,- zs)} (os {x} {ys} {zs} th) f rewrite oe-unique (oe -<- th) =  f x (os oe) ,-_ $= selectTabulate th \ i x1 -> f i (o' x1)
  selectTabulate {I} {P} {.[]} {.[]} oz f = refl

-- MARK: 6/6

  -- Construct the proof that all elements of a list have the property
  -- of being somewhere in the list.

  positions : (is : List I) -> All (_<- is) is
  positions is = tabulate is \ i z -> z

  -- Construct a natural transformation which extracts the only element
  -- from an All P (i ,- [])

  onlyNTtransform : forall {I} (X : I -> Set) (i : I) ->
                  All X (i ,- []) -> X i
  onlyNTtransform X i (x ,- []) = x

  onlyNTnatural : forall {I} {X Y : I -> Set}
                       (f : (i : I) -> X i -> Y i) (x : I) (x1 : All X (x ,- [])) ->
                f x (onlyNTtransform X x x1) ==
                onlyNTtransform Y x (all f (x ,- []) x1)
  onlyNTnatural f x (x1 ,- []) = refl

  onlyNT : NaturalTransformation
            (ALL I -Func- Reindex (_,- []) SET)
            (ID (I -C> SET))
  onlyNT = record
           { transform = onlyNTtransform
           ; natural = \ f -> ext \ x -> ext \ x1 -> onlyNTnatural f x x1 
           }

-- MARK: 2/2

  -- From these components, assemble the natural transformation which projects
  -- one element from a bunch. That is, if we have (x : i <- is) and we have
  -- Ps for all the is, then we should certainly have a P i.

  projectNTnatural : forall {I} (i : I) (is : List I)
                          (x : i ,- [] <: is) (X Y : I -> Set) (f : (i₁ : I) -> X i₁ -> Y i₁)
                          (x1 : All X is) ->
                   f i (onlyNTtransform X i (select x x1)) ==
                   onlyNTtransform Y i (select x (all f is x1))
  projectNTnatural i is x X Y f x1 = {!!}

  projectNT : {i : I}{is : List I}(x : i <- is) ->
              NaturalTransformation (ALL I -Func- Point SET is) (Point SET i)
  transform (projectNT {i} x) X x1 = transform onlyNT X i (transform (selectNT x) X x1)
  natural (projectNT {i} {is} x) {X} {Y} f = ext \ x1 -> projectNTnatural i is x X Y f x1

  -- Show that tabulating projections is the identity.

  tabulateProject : {P : I -> Set}{is : List I}(ps : All P is) ->
    tabulate is (\ i x -> transform (projectNT x) P ps) == ps
  tabulateProject ps = {!!}

  -- Show that projecting from a tabulation applies the tabulated function.

  projectTabulate : {P : I -> Set}{is : List I}
    (f : (i : I) -> i <- is -> P i)
    {i : I}(x : i <- is) ->
    transform (projectNT x) P (tabulate is f) == f i x
  projectTabulate f x = {!!}

  -- A useful way to show that two "All" structures are equal is to show that
  -- they agree at each projection. Make it so! Hint: tabulateProject.

  eqAll : {P : I -> Set}{is : List I}{ps0 ps1 : All P is} ->
    ((i : I)(x : i <- is) ->
      transform (projectNT x) P ps0 == transform (projectNT x) P ps1) ->
    ps0 == ps1
  eqAll {ps0 = ps0}{ps1 = ps1} q = {!!}
  


------------------------------------------------------------------------------
-- HOW TO CUT THINGS UP
------------------------------------------------------------------------------

record _<|_ (O{-utside-} I{-nside-} : Set) : Set where
  constructor _<!_
  field
    Cuts    : O -> Set  -- for every Outside, there is a set of ways to cut it
    pieces  : {o : O} -> Cuts o -> List I
                        -- into a bunch of pieces which are Inside

-- This information amounts to giving an indexed container with finitely
-- many positions. As a consequence, we can use All to collect the
-- substructures which fill the pieces inside.

module _ {O I : Set} where

  open Category
  open Functor
  open _<|_

  [[_]]Cr : O <| I -> (I -> Set)   -- what's filling the insides?
                   -> (O -> Set)
  [[ Cu <! ps ]]Cr P o =      Sg (Cu o) \ c   -- choose your cut
                           -> All P (ps c)    -- then fill all the insides

  -- Extend [[_]]Cr to a Functor.

  [[_]]CrF : (F : O <| I) ->
               Functor (I -C> SET) (O -C> SET) [[ F ]]Cr
  [[ Cu <! ps ]]CrF = {!!}


  -- Meanwhile, there is a concrete way to represent natural transformations
  -- between two such functors.
  
  Cutmorph : (F G : O <| I) -> Set
  Cutmorph (Cu <! ps) G =
    (o : O)(cu : Cu o)             -- given a source cut
      -> [[ G ]]Cr (_<- ps cu) o   -- choose a target cut, and say which source
                                   -- piece goes in each target position

  module _ (F G : O <| I) where

    open NaturalTransformation
    module GF = Functor [[ G ]]CrF

    -- Show that every Cutmorph induces a natural transformation.
    -- Proving it is natural is an opportunity to deploy eqAll.

    CutmorphNT : Cutmorph F G ->  NaturalTransformation  [[ F ]]CrF  [[ G ]]CrF
    CutmorphNT m = {!!}

    -- Extract a Cutmorph from an arbitrary natural transformation by choosing
    -- a suitable element type.

    ntCutmorph : NaturalTransformation  [[ F ]]CrF  [[ G ]]CrF  -> Cutmorph F G
    ntCutmorph k = {!!}

  -- Construct identity and composition for Cutmorphs. Hint: you've done the
  -- hard work already.

  idCutmorph : {F : O <| I} -> Cutmorph F F
  idCutmorph = {!!}

  _-Cutmorph-_ : {F G H : O <| I} -> Cutmorph F G -> Cutmorph G H -> Cutmorph F H
  fg -Cutmorph- gh = {!!}

  -- We have left the following goal commented out, because it involves more heat
  -- than light.
  -- CUTMORPH : Category Cutmorph
  -- CUTMORPH = ?


------------------------------------------------------------------------------
-- HOW TO CUT THINGS UP INTO LOTS OF LITTLE TINY PIECES
------------------------------------------------------------------------------

module _ {I : Set}(F : I <| I) where

  -- If the insides have the same index type as the outsides, we can cut and
  -- cut again.

  data Tree (X : I -> Set)(i : I) : Set where
    leaf : X i -> Tree X i
    <_> : [[ F ]]Cr (Tree X) i -> Tree X i

  -- The following wrap the constructors as arrows in I -C> SET.
  
  iLeaf : {X : I -> Set} -> [ X -:> Tree X ]
  iLeaf i = leaf
  iNode : {X : I -> Set} -> [ [[ F ]]Cr (Tree X) -:> Tree X ]
  iNode i = <_>

  module _ {X Y : I -> Set}             -- Suppose we can turn ...
           (l : [ X -:> Y ])            -- ... leaves into Ys, and ...
           (n : [ [[ F ]]Cr Y -:> Y ])  -- ... nodes made of Ys into Ys.
         where

    -- Show that we can turn whole trees into Ys.
    -- You will need to inline functoriality of All to get the
    --   termination checker to shut up.

    treeIter : [ Tree X -:> Y ]
    allTreeIter : [ All (Tree X) -:> All Y ]
    treeIter i xt = {!!}
    allTreeIter is xts = {!!}


  module _ where
    open Category (I -C> SET)

    -- Use treeIter, rather than pattern matching, to construct the following
    -- operation which should preserve nodes and graft on more tree at the leaves.

    treeBind : {X Y : I -> Set} -> [ X -:> Tree Y ] -> [ Tree X -:> Tree Y ]
    treeBind k = {!!}

    -- Use treeBind to implement "map" and "join" for trees.
    -- They're one-liners.

    tree : {X Y : I -> Set} -> [ X -:> Y ] -> [ Tree X -:> Tree Y ]
    tree f = {!!}

    treeJoin : {X : I -> Set} -> [ Tree (Tree X) -:> Tree X ]
    treeJoin = {!!}


    -- Show that replacing leaves by leaves and nodes by nodes achieves little.
    -- This will need a proof by induction.

    treeIterId : {X : I -> Set} -> treeIter (iLeaf {X = X}) iNode == idArr
    treeIterId = {!!}


  -- The following result will be of considerable assistance.

  module _ {W X Y : I -> Set}
           (k : [ W -:> Tree X ])       -- how to grow more tree
           (l : [ X -:> Y ])            -- how to eat leaves
           (n : [ [[ F ]]Cr Y -:> Y ])  -- how to eat nodes
           where
    open Category (I -C> SET)

    -- Show that growing a tree with treeBind then eating the result
    -- gives the same as eating the original with more eating at the leaves.

    treeBindIter : (treeBind k -arr- treeIter l n)
                     ==
                   treeIter (k -arr- treeIter l n) n
    treeBindIter = {!!}

  -- Suitably tooled up, go for the win.

  module _  where
    open Category (I -C> SET)
    open Functor
    open NaturalTransformation
    open Monad

    -- You have implemented "map" and "join".
    -- Prove that you have a functor and a monad.

    TREE : Functor (I -C> SET) (I -C> SET) Tree
    map TREE = tree
    mapidArr TREE = {!!}
    map-arr- TREE = {!!}

    treeMonad : Monad TREE
    transform (returnNT treeMonad) X = iLeaf
    natural (returnNT treeMonad) = {!!}
    transform (joinNT treeMonad) X = treeJoin
    natural (joinNT treeMonad) = {!!}
    returnJoin treeMonad = {!!}
    mapReturnJoin treeMonad = {!!}
    joinJoin treeMonad = {!!}
    

------------------------------------------------------------------------------
-- AND RELAX
------------------------------------------------------------------------------

-- If "outsides" are a numerical size z,
-- we might cut them into two pieces whose sizes add up to z.

NatCut : Nat <| Nat
NatCut = (\ z -> Sg Nat \ x -> Sg Nat \ y -> (x +N y) == z)
      <! (\ { (x , y , _) -> x ,- y ,- []})

twoToThe : Nat -> Nat
twoToThe zero     = 1
twoToThe (suc n)  = twoToThe n +N twoToThe n

-- You have to make a big tree out of Xs, but you have only an X of size 1.
-- There is more than one right answer.

bigTree : (X : Nat -> Set) -> X 1 -> (n : Nat) -> Tree NatCut X (twoToThe n)
bigTree X x n = {!!}

-- We'll see more of Tree and NatCut next time...


------------------------------------------------------------------------------
-- END OF EXERCISE TWO
------------------------------------------------------------------------------
