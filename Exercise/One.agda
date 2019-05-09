-- TOTAL MARK: 50/50 (so far)
{-# OPTIONS --allow-unsolved-metas #-}
module Exercise.One where

open import Lib.Basics
open import Lib.Nat

------------------------------------------------------------------------------
-- ORDER-PRESERVING EMBEDDINGS (or "thinnings" for short)
------------------------------------------------------------------------------

-- The type xs <: ys represents the possible order-preserving
-- embeddings from xs to ys. That means ys is generated by
-- inserting more stuff anywhere in xs, i.e. "thinning" xs.

data _<:_ {X : Set} : List X -> List X -> Set where
  o' : forall {x ys zs} -> ys <: zs ->       ys  <:  x ,- zs  -- insert new
  os : forall {x ys zs} -> ys <: zs ->  x ,- ys  <:  x ,- zs  -- keep old
  oz :                                    []     <:    []     -- done!

infix 50 _<:_

-- You can also think of xs <: ys as the ways of selecting
-- elements xs from ys, with
--   o' meaning "drop the head",
--   os meaning "take the head",
--   oz meaning "end of list".

-- You can also see a thinning in xs <: ys as a vector of bits
-- telling whether each element position in ys is connected
-- from an element position in xs.

--              2 ,-      4 ,- []
--    o'  (o'  (os  (o'  (os   oz))))
--    0 ,- 1 ,- 2 ,- 3 ,- 4 ,- []


------------------------------------------------------------------------------
-- Exploration (for comprehension rather than credit)
------------------------------------------------------------------------------

-- Lists of elements of One are a lot like numbers

num : Nat -> List One
num zero    = []
num (suc n) = <> ,- num n

-- Using C-c C-a with -l and -s options, generate exhaustive lists of
-- thinnings with the following types.

pick0from4 : List (num 0 <: num 4)
pick0from4 = o' (o' (o' (o' oz))) ,- [] -- o' (o' (o' (o' oz))) ,- []

pick1from4 : List (num 1 <: num 4)
pick1from4 = o' (os (o' (o' oz))) ,- [] -- o' (os (o' (o' oz))) ,- []

pick2from4 : List (num 2 <: num 4)
pick2from4 = o' (o' (os (os oz))) ,- []

pick3from4 : List (num 3 <: num 4)
pick3from4 = o' (os (os (os oz))) ,- []
          
pick4from4 : List (num 4 <: num 4)
pick4from4 = os (os (os (os oz))) ,- []

-- F: You were meant to list all solutions, but ok

-- But with more interesting elements, we have fewer options, sometimes.

thinOdds : List (1 ,- 3 ,- 5 ,- [] <: 0 ,- 1 ,- 2 ,- 3 ,- 4 ,- 5 ,- 6 ,- [])
thinOdds = o' (os ( o' ( os (o' (os (o' oz)))))) ,- []

-- MARK: 2/2

------------------------------------------------------------------------------
-- 1.1 Categorical Structure
------------------------------------------------------------------------------

-- Construct the identity thinning from any list to itself.

oi : forall {X}{xs : List X} -> xs <: xs
oi {X} {[]} = oz
oi {X} {x ,- xs} = os oi

-- Give composition for thinnings. Minimize the number of cases.

_-<-_ : forall {X}{xs ys zs : List X} -> xs <: ys -> ys <: zs -> xs <: zs
th -<- o' ph = o' (th -<- ph)
o' th -<- os ph = o' (th -<- ph)
os th -<- os ph = os (th -<- ph)
th -<- oz = th



infixl 40 _-<-_

-- Prove the following laws. Minimize the number of cases (which will
-- depend on your definition of _-<-_).
oi-<- : forall {X}{xs ys : List X}(ph : xs <: ys) -> oi -<- ph == ph
oi-<- (o' ph) = o' $= oi-<- ph
oi-<- (os ph) = os $= oi-<- ph
oi-<- oz = refl

  
_-<-oi : forall {X}{xs ys : List X}(th : xs <: ys) -> th -<- oi == th
_-<-oi (o' th) = o' $= (th -<-oi)
_-<-oi (os th) = os $= (th -<-oi)
oz -<-oi = refl



assoc-<- : forall {X}{ws xs ys zs : List X}
             (th0 : ws <: xs)(th1 : xs <: ys)(th2 : ys <: zs) ->
             (th0 -<- th1) -<- th2 == th0 -<- (th1 -<- th2)

assoc-<- th0 th1 (o' th2) =
  o' (th0 -<- th1 -<- th2)
    =[ o' $= assoc-<- th0 th1 th2  >=
  o' (th0 -<- (th1 -<- th2))
    [QED]
assoc-<- th0 (o' th1) (os th2) =
  o' (th0 -<- th1 -<- th2)
    =[ o' $= assoc-<- th0 th1 th2 >=
  o' (th0 -<- (th1 -<- th2))
    [QED]
assoc-<- (o' th0) (os th1) (os th2) =
  o' (th0 -<- th1 -<- th2)
    =[ o' $= assoc-<- th0 th1 th2 >=
  o' (th0 -<- (th1 -<- th2))
    [QED]
assoc-<- (os th0) (os th1) (os th2) =
  os (th0 -<- th1 -<- th2)
    =[ os $= assoc-<- th0 th1 th2 >=
  os (th0 -<- (th1 -<- th2))
    [QED]
assoc-<- th0 th1 oz = refl

-- MARK: 8/8

------------------------------------------------------------------------------
-- 1.2 Emptiness
------------------------------------------------------------------------------

-- Show that the empty list embeds into all lists in a unique way.

oe : forall {X}{xs : List X} -> [] <: xs
oe {X} {[]} = oz
oe {X} {x ,- xs} = o' oe

oe-unique : forall {X}{xs : List X}(th : [] <: xs) -> th == oe
oe-unique (o' th) =
  o' th
    =[ o' $= oe-unique th  >=
  o' oe
    [QED]
oe-unique oz = refl

-- MARK: 6/6

------------------------------------------------------------------------------
-- 1.3 Antisymmetry
------------------------------------------------------------------------------

-- Show that if two lists are mutually embeddable, they are equal
-- and the embeddings are the identity.

antisym : forall {X}{xs ys : List X}
             (th : xs <: ys)(ph : ys <: xs) -> 
             Sg (xs == ys) \
             { refl -> th == oi * ph == oi }
antisym (o' th) (o' ph) with antisym (o' oi -<- th) (o' oi -<- ph)
antisym (o' th) (o' (o' ph)) | refl , fst , ()
antisym (o' th) (o' (os ph)) | refl , fst₁ , ()
antisym (o' th) (os ph) with antisym ph (o' oi -<- th)
antisym (o' th) (os (o' ph)) | refl , () , snd
antisym (o' (o' th)) (os (os .oi)) | refl , refl , ()
antisym (o' (os th)) (os (os .oi)) | refl , refl , ()
antisym (o' ()) (os oz) | refl , refl , snd
antisym (os th) (o' ph) with antisym th (o' oi -<- ph)
antisym (os th) (o' (o' ph)) | refl , fst₁ , ()
antisym (os th) (o' (os ph)) | refl , fst₁ , ()
antisym (os th) (os ph) with antisym th ph
antisym (os th) (os ph) | refl , fst , snd = refl , (os $= fst) , (os $= snd)
antisym oz oz = refl , refl , refl


-- Deduce that oi is unique.

oi-unique : forall {X}{xs : List X}(th : xs <: xs) -> th == oi
oi-unique th with antisym th th
oi-unique th | refl , p , q = p
{-
oi-unique (o' th) with oi-unique (o' oi -<- th)
oi-unique (o' (o' th)) | ()
oi-unique (o' (os th)) | ()
oi-unique (os th) = os $= oi-unique th
oi-unique oz = refl
-}

-- MARK: 6/6

------------------------------------------------------------------------------
-- 1.4 Thinnings as selections
------------------------------------------------------------------------------

-- We can use the "selection" interpretation of thinnings to act
-- on data indexed by lists.
-- The type All P ys has elements of type P y for each y in ys.
-- If xs <: ys, show that we can get P x for each x in xs.

select : forall {X}{xs ys : List X}{P : X -> Set} ->
         xs <: ys -> All P ys -> All P xs
select (o' th) (x ,- pys) = select th pys
select (os th) (x ,- pys) = x ,- select th pys
select oz pys = pys 

-- Now prove the following laws relating to selecting by the
-- identity and composition.

select-oi : forall {X}{xs : List X}{P : X -> Set} -> (pxs : All P xs) ->
            select oi pxs == pxs
select-oi [] = refl
select-oi (x ,- pxs) = (x ,-_) $= select-oi pxs

select-<- : forall {X}{xs ys zs : List X}{P : X -> Set} ->
            (th : xs <: ys)(ph : ys <: zs) -> (pzs : All P zs) ->
            select (th -<- ph) pzs == select th (select ph pzs)
select-<- th oz [] = refl
select-<- th (o' ph) (x ,- pzs) = select-<- th ph pzs
select-<- (o' th) (os ph) (x ,- pzs) = select-<- th ph pzs
select-<- (os th) (os ph) (x ,- pzs) = x ,-_ $= select-<- th ph pzs

-- MARK: 8/8

------------------------------------------------------------------------------
-- 1.5 Splittings
------------------------------------------------------------------------------

-- If we have two thinnings,
--   th : xs <: zs
--   ph : ys <: zs
-- we can say what it means for th and ph to *split* zs:
-- every element position in zs is connected from either
-- a position in xs or from a position in ys, but *not both*.

data Splitting {X : Set} : {xs ys zs : List X}
                           (th : xs <: zs)(ph : ys <: zs) 
                           -> Set where
  split's : forall {w xs ys zs}{th : xs <: zs}{ph : ys <: zs} ->
             Splitting th ph ->
             Splitting {zs = w ,- _} (o' th) (os ph)
  splits' : forall {w xs ys zs}{th : xs <: zs}{ph : ys <: zs} ->
             Splitting th ph ->
             Splitting {zs = w ,- _} (os th) (o' ph)
  splitzz : Splitting oz oz

-- Show that if we know how xs <: zs, we can find a splitting of zs by
-- computing...

thinSplit : {X : Set}{xs zs : List X}(th : xs <: zs) ->
            Sg (List X) \ ys ->    -- ...what wasn't from xs...
            Sg (ys <: zs) \ ph ->  -- ...but was in zs...
            Splitting th ph        -- ...hence forms a splitting.
thinSplit {zs = []} oz = [] , oz , splitzz
thinSplit {zs = x ,- zs} (o' th) with thinSplit th
thinSplit {xs = _} {x ,- .(_ ,- _)} (o' (o' th)) | _ , _ , p = _ ,- _ , _ , split's p
thinSplit {xs = _} {x ,- .(_ ,- _)} (o' (os th)) | fst₁ , fst₂ , snd₁ = x ,- fst₁ , os fst₂ , split's snd₁
thinSplit {xs = _} {x ,- .[]} (o' oz) | fst₁ , fst₂ , snd₁ = x ,- fst₁ , os fst₂ , split's snd₁
thinSplit {zs = x ,- zs} (os th) with thinSplit th
thinSplit {_} {_} {x ,- .(_ ,- _)} (os (o' th)) | fst₁ , fst₂ , snd₁ = fst₁ , o' fst₂ , splits' snd₁
thinSplit {_} {_} {x ,- .(_ ,- _)} (os (os th)) | fst₁ , fst₂ , snd₁ = fst₁ , o' fst₂ , splits' snd₁
thinSplit {_} {_} {x ,- .[]} (os oz) | fst₁ , fst₂ , snd₁ = fst₁ , o' fst₂ , splits' snd₁

-- F: Variable names could be better

-- Given a splitting, show that we can "riffle" together a bunch
-- of "All P"-s for each selection to get an "All P" for the whole.

riffle : forall {X : Set}{xs ys zs : List X}
                {th : xs <: zs}{ph : ys <: zs}
                {P : X -> Set} ->
                All P xs -> Splitting th ph -> All P ys ->
                All P zs
riffle pxs (split's s) (x ,- pys) = x ,- riffle pxs s pys
riffle (x ,- pxs) (splits' s) pys = x ,- riffle pxs s pys 
riffle pxs splitzz pys = pys

-- Moreover, we can use a splitting to invert "riffle", dealing
-- out an "All P" for the whole list into the parts for each
-- selection in the splitting, and making sure that the parts
-- riffle back together to make the whole.

data Deal {X : Set}{xs ys zs : List X}
          {th : xs <: zs}{ph : ys <: zs}(s : Splitting th ph)
          {P : X -> Set} :
            All P zs -> Set where
  dealt : (pxs : All P xs)(pys : All P ys) -> Deal s (riffle pxs s pys)

deal : {X : Set}{xs ys zs : List X}
       {th : xs <: zs}{ph : ys <: zs}(s : Splitting th ph)
       {P : X -> Set}(pzs : All P zs) -> Deal s pzs
deal (split's s) (x ,- pzs) with deal s pzs
deal (split's s) (x ,- .(riffle pxs s pys)) | dealt pxs pys = dealt pxs (x ,- pys)
deal (splits' s) (x ,- pzs) with deal s pzs
deal (splits' s) (x ,- .(riffle pxs s pys)) | dealt pxs pys = dealt (x ,- pxs) pys
deal splitzz [] = dealt [] []

-- MARK: 10/10

------------------------------------------------------------------------------
-- 1.6 Composability as a relation
------------------------------------------------------------------------------

-- We have the composition *operator*, but it is sometimes more
-- convenient to work with the *call graph* of the composition operator,
-- giving the explanations for why an output comes from some input.

-- For example, the call graph of our boolean <= operator from Lecture.One
--   _<=_ : Nat -> Nat -> Two
--   zero <= y = tt
--   suc x <= zero = ff
--   suc x <= suc y = x <= y

-- would be
--   data Graph<= : Nat -> Nat -> Two -> Set where
--     le-z-y : forall {y} -> Graph<= zero    y    tt
--     le-s-z : forall {x} -> Graph<= (suc x) zero ff
--     le-s-s : forall {x y b} -> Graph<= x y b -> Graph<= (suc x) (suc y) b

-- so that we can always show
--   graph<= : (x y : Nat) -> Graph<= x y (x <= y)

-- Define the inductive composability relation on three thinnings.
-- This should correspond to your composition function, with one
-- constructor per line of your function, and one recursive substructure
-- per recursive call. We've written the type declaration, but you need
-- to add the constructors.

-- No defined function symbols should appear in any of the type indices,
-- just variables and constructors. That means dependent pattern matching
-- will play nice.

{-
_-<-_ : forall {X}{xs ys zs : List X} -> xs <: ys -> ys <: zs -> xs <: zs
th -<- o' ph = o' (th -<- ph)
o' th -<- os ph = o' (th -<- ph)
os th -<- os ph = os (th -<- ph)
th -<- oz = th
-}


data Composable-<- {X : Set}
     : {xs ys zs : List X}
       (th : xs <: ys)(ph : ys <: zs)(thph : xs <: zs)
       -> Set where
     comp-th-oph : {z : X}{xs ys zs : List X}(th : xs <: ys)(ph : ys <: zs)(thph : xs <: zs)
      -> Composable-<- th ph thph -> Composable-<- {zs = z ,- zs} th (o' ph) (o' thph)
     comp-oth-osph : {y : X}{xs ys zs : List X}(th : xs <: ys)(ph : ys <: zs)(thph : xs <: zs)
      -> Composable-<- th ph thph -> Composable-<- {ys = y ,- ys} (o' th) (os ph) (o' thph)
     comp-osth-osph : {x : X}{xs ys zs : List X}(th : xs <: ys)(ph : ys <: zs)(thph : xs <: zs)
      -> Composable-<- th ph thph -> Composable-<- {xs = x ,- xs} (os th) (os ph) (os thph)
     comp-oz-oz : Composable-<- oz oz oz

-- Show that your definition really captures composability by
-- proving the following.


composable-<- : forall {X : Set}{xs ys zs : List X}
                (th : xs <: ys)(ph : ys <: zs) ->
                Composable-<- th ph (th -<- ph)
  -- i.e., we have *at least* composition...
composable-<- th (o' ph) = comp-th-oph th ph (th -<- ph) (composable-<- th ph)
composable-<- (o' th) (os ph) = comp-oth-osph th ph (th -<- ph) (composable-<- th ph)
composable-<- (os th) (os ph) = comp-osth-osph th ph (th -<- ph) (composable-<- th ph)
composable-<- oz oz = comp-oz-oz 

composable-unique : forall {X : Set}{xs ys zs : List X}
                    {th : xs <: ys}{ph : ys <: zs}
                    {thph thph' : xs <: zs} ->
                    Composable-<- th ph thph ->
                    Composable-<- th ph thph' ->
                    thph == thph'
  -- ...and nothing but composition.
composable-unique (comp-th-oph th ph thph c) (comp-th-oph .th .ph thph1 d) = o' $= composable-unique c d
composable-unique (comp-oth-osph th ph thph c) (comp-oth-osph .th .ph thph1 d) = o' $= composable-unique c d
composable-unique (comp-osth-osph th ph thph c) (comp-osth-osph .th .ph thph1 d) = os $= composable-unique c d
composable-unique comp-oz-oz comp-oz-oz = refl

-- Your prize for establishing the graph representation is to have a nice time
-- showing that thinnings really are *embeddings* (or "monomorphisms").
-- If you have two thinnings, th and th' that compose with some ph to get
-- equal results, th and th' must have been equal in the first place. That
-- tells you something important about ph, namely that it maps all its source
-- positions to distinct target positions.

composable-mono : forall {X}{xs ys zs : List X}
  {th th' : xs <: ys}{ph : ys <: zs}{ps : xs <: zs} ->
  Composable-<- th ph ps -> Composable-<- th' ph ps ->
  th == th'
composable-mono (comp-th-oph th ph thph c) (comp-th-oph th₁ .ph .thph d) = composable-mono c d
composable-mono (comp-oth-osph th ph thph c) (comp-oth-osph th₁ .ph .thph d) = o' $= composable-mono c d
composable-mono (comp-osth-osph th ph thph c) (comp-osth-osph th₁ .ph .thph d) = os $= composable-mono c d 
composable-mono comp-oz-oz comp-oz-oz = refl 

-- Now use composable-<- and composable-mono to get a cheap proof of the
-- following.

mono-<- : forall {X}{xs ys zs : List X}(th th' : xs <: ys)(ph : ys <: zs) ->
             th -<- ph == th' -<- ph ->
             th == th'
mono-<- th th' ph q with composable-<- th ph
... | thph with composable-<- th' ph
... | th'ph rewrite q = composable-mono thph th'ph 

-- F: should be a one-liner
-- B: i was literlay a rewrite away compared to or meeting ... sad times 

-- MARK: 10/10

------------------------------------------------------------------------------
-- 1.7 Pullbacks (pointwise "and")
------------------------------------------------------------------------------
-- F: 10 marks (out of 60)

-- If we have a situation like this

--
--                ys
--                |
--                | ph
--                v
--     xs ------> zs
--           th

-- we say a "BackSquare" extends the situation to a square

--         side1
-- corner ------> ys
--      |         |
-- side0|         | ph
--      v         v
--     xs ------> zs
--           th

-- where the *same* diagonal is both side0 -<- th and side1 -<- ph,
-- so either path around the square gives the same thinning.

record BackSquare {X}{xs ys zs : List X}
              (th : xs <: zs)(ph : ys <: zs) : Set where
  constructor backSquare
  field
    {corner}   : List X
    {side0}    : corner <: xs
    {side1}    : corner <: ys
    {diagonal} : corner <: zs
    triangle0  : Composable-<- side0 th diagonal
    triangle1  : Composable-<- side1 ph diagonal

open BackSquare

-- The corner of the "best" BackSquare is called a *pullback*,
-- (and the square is called a "pullback square"). What's best
-- about it is that the corner of every other BackSquare embeds
-- in it. That is, it has all the things that both th and ph
-- select from zs.

-- First, construct the pullback square.

-- like antysim build up from bottom to top 

pullback-<- : forall {X}{xs ys zs : List X} ->
              (th : xs <: zs)(ph : ys <: zs) ->
              BackSquare th ph
pullback-<- (o' th) (o' ph) with pullback-<- th ph
pullback-<- (o' th) (o' ph) | backSquare {side0 = side2} {side3} {diagonal₁} triangle2 triangle3 = backSquare (comp-th-oph side2 th diagonal₁ triangle2)
                                                                                                     (comp-th-oph side3 ph diagonal₁ triangle3)
pullback-<- (os th) (o' ph) with pullback-<- th ph
pullback-<- (os th) (o' ph) | backSquare {side0 = side2} {side3} {diagonal₁} triangle2 triangle3 = backSquare (comp-oth-osph side2 th diagonal₁ triangle2)
                                                                                                     (comp-th-oph side3 ph diagonal₁ triangle3)
pullback-<- (o' th) (os ph) with pullback-<- th ph
pullback-<- (o' th) (os ph) | backSquare {side0 = side2} {side3} {diagonal₁} triangle2 triangle3 = backSquare (comp-th-oph side2 th diagonal₁ triangle2)
                                                                                                     (comp-oth-osph side3 ph diagonal₁ triangle3)
pullback-<- (os th) (os ph) with pullback-<- th ph
pullback-<- (os th) (os ph) | backSquare {side0 = side2} {side3} {diagonal₁} triangle2 triangle3 = backSquare (comp-osth-osph side2 th diagonal₁ triangle2)
                                                                                                     (comp-osth-osph side3 ph diagonal₁ triangle3)
pullback-<- oz oz = backSquare comp-oz-oz comp-oz-oz

-- F: Hint: pullback-<- (os th) (os ph) is not quite right

-- Then show that every other BackSquare has a corner
-- which embeds in the pullback, and that the resulting
-- triangles commute.

pullback-best : forall {X}{xs ys zs : List X} ->
                {th : xs <: zs}{ph : ys <: zs} ->
                let bs = pullback-<- th ph in
                (bs' : BackSquare th ph) ->
                Sg (corner bs' <: corner bs) \ ps ->
                Composable-<- ps (side0 bs) (side0 bs') *
                Composable-<- ps (side1 bs) (side1 bs')
pullback-best (backSquare (comp-th-oph th ph thph triangle2) (comp-th-oph th₁ ph₁ .thph triangle3)) with pullback-best (backSquare triangle2 triangle3)
pullback-best (backSquare (comp-th-oph th ph thph triangle2) (comp-th-oph th₁ ph₁ .thph triangle3)) | fst1 , fst2 , snd = fst1 , (fst2 , snd)
pullback-best (backSquare (comp-th-oph th ph thph triangle2) (comp-oth-osph th₁ ph₁ .thph triangle3)) with pullback-best (backSquare triangle2 triangle3)
pullback-best (backSquare (comp-th-oph th ph thph triangle2) (comp-oth-osph th₁ ph₁ .thph triangle3)) | fst1 , fst2 , snd = fst1 , (fst2 , comp-th-oph fst1 _ th₁ snd)
pullback-best (backSquare (comp-oth-osph th ph thph triangle2) (comp-th-oph th₁ ph₁ .thph triangle3)) with pullback-best (backSquare triangle2 triangle3)
pullback-best (backSquare (comp-oth-osph th ph thph triangle2) (comp-th-oph th₁ ph₁ .thph triangle3)) | fst1 , fst2 , snd = fst1 , (comp-th-oph fst1 _ th fst2 , snd)
pullback-best (backSquare (comp-oth-osph th ph thph triangle2) (comp-oth-osph th₁ ph₁ .thph triangle3)) with pullback-best (backSquare triangle2 triangle3)
pullback-best (backSquare (comp-oth-osph th ph thph triangle2) (comp-oth-osph th₁ ph₁ .thph triangle3)) | fst1 , fst2 , snd = o' fst1 , (comp-oth-osph fst1 _ th fst2 , comp-oth-osph fst1 _ th₁ snd)
pullback-best (backSquare (comp-osth-osph th ph thph triangle2) (comp-osth-osph th₁ ph₁ .thph triangle3)) with pullback-best (backSquare triangle2 triangle3 )
pullback-best (backSquare (comp-osth-osph th ph thph triangle2) (comp-osth-osph th₁ ph₁ .thph triangle3)) | fst1 , fst2 , snd = os fst1 , comp-osth-osph fst1 _ th fst2 , comp-osth-osph fst1 _ th₁ snd
pullback-best (backSquare comp-oz-oz comp-oz-oz) = oz , comp-oz-oz , comp-oz-oz
