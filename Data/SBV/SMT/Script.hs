----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.Script
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- A script is a simply a String. This module serves as a place-holder
-- for future work where we might want to replace it with something
-- with more structure, for either efficiency or other purposes.
--
-- We follow the naming in Text.PrettyPrint.HugesPJ closely
-- for mnemonic value.
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}

module Data.SBV.SMT.Script(
                Script
              , render
              , empty
              , ($$), vcat
              , (<>), (<+>), hsep
              , parens, hang
              , text
              , int
              , integer
        ) where

import Data.List (intercalate)

type Script = String

-- | Convert 'Script' to flat 'String', as fast as possible!
render :: String -> String
render = id

-- | Empty script
empty :: Script
empty = ""
{-# INLINE empty #-}

-- | Vertical concat
($$) :: Script -> Script -> Script
a $$ b = a ++ "\n" ++ b
infixl 5 $$
{-# INLINE ($$) #-}

-- | Vertical concat of multiple scripts
vcat :: [Script] -> Script
vcat = foldr ($$) empty
{-# INLINE vcat #-}

-- | Horizontal separated concat of multiple scripts
hsep :: [Script] -> Script
hsep = intercalate " "
{-# INLINE hsep #-}

-- | Horizontal concat
(<>) :: Script -> Script -> Script
a <> b = hsep [a, b]
infixl 6 <>
{-# INLINE (<>) #-}

-- | Spacing horizontal concat
(<+>) :: Script -> Script -> Script
a <+> b = hsep [a, b]
infixl 6 <+>
{-# INLINE (<+>) #-}

-- | Nesting
hang :: Script -> Int -> Script -> Script
hang a i b = a ++ go b
 where tab = '\n' : replicate i ' '
       go ('\n':cs) = tab ++ go cs
       go (c:cs)    = c : go cs
       go ""        = ""
{-# INLINE hang #-}

-- | Parenthesized script
parens :: Script -> Script
parens s = '(' : s ++ ")"
{-# INLINE parens #-}

-- | Literal conversion
text :: String -> Script
text = id
{-# INLINE text #-}

-- | Int conversion
int :: Int -> Script
int = show
{-# INLINE int #-}

-- | Integer conversion
integer :: Integer -> Script
integer = show
{-# INLINE integer #-}
