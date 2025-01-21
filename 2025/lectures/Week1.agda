module Week1 where

{-------------------------
-- Administrative Details
-------------------------}

-- | The Team

-- Guillaume Allais
-- Conor McBride
-- Fredrik Nordvall Forsberg
-- Sean Watters

-- | The Events

-- * Lectures
-- Mondays   | 10am   to 11am   | TL565
-- Tuesdays  | 2pm    to 3pm    | TG227

-- * Labs
-- Announced tomorrow.
-- Special help-me-install-Agda lab today after this lecture in LT1201.

-- | Assessment

-- Coursework only.
-- 2 courseworks (40% and 60%)

-- | Lecture materials

-- Results of live programming on Github
-- Video recordings
-- Please tell us what you think in One-Minute Papers!

{-------------------------
-- Content starts here
-------------------------}

-- Lists

data List (X : Set) : Set where
  [] : List X
  _,-_ : X -> List X -> List X

append : {X : Set} -> List X -> List X -> List X
append [] ys = ys
append (x ,- xs) ys = x ,- append xs ys


-- zap

zap : {S T : Set} -> List (S -> T) -> List S -> List T
zap [] [] = []
zap [] (s ,- ss) = []
zap (f ,- fs) [] = []
zap (f ,- fs) (s ,- ss) = f s ,- zap fs ss

-- head and tail

tail : {X : Set} -> List X -> List X
tail [] = []
tail (x ,- xs) = xs

head : {X : Set} -> List X -> X
head [] = {!!}
head (x ,- xs) = x

-- ...
