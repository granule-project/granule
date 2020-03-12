-- {
-- {-# OPTIONS_GHC -w #-}
--
-- {-# LANGUAGE DeriveGeneric #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}
--
-- module Language.Granule.Syntax.Lexer (Token(..),scanTokens,getPos,
--                      getPosToSpan,symString,constrString) where
-- import Language.Granule.Syntax.Expr
-- import Language.Granule.Syntax.FirstParameter
-- import GHC.Generics (Generic)
-- import Data.Text (Text)
--
-- }
--
-- %wrapper "posn"
--
-- $digit  = 0-9
-- $alpha  = [a-zA-Z\_\-\=]
-- $lower  = [a-z]
-- $upper  = [A-Z]
-- $eol    = [\n]
-- $alphanum  = [$alpha $digit \_]
-- $fruit = [\127815-\127827] -- 🍇🍈🍉🍊🍋🍌🍍🍎🍏🍐🍑🍒🍓
-- @sym    = $lower ($alphanum | \')* | $fruit
-- @constr = ($upper ($alphanum | \')* | \(\))
-- @float   = \-? $digit+ \. $digit+
-- @int    = \-? $digit+
-- @charLiteral = \' ([\\.]|[^\']| . ) \'
-- @stringLiteral = \"(\\.|[^\"]|\n)*\"
-- @importFilePath = ($alphanum | \' | \.)*
--
-- tokens :-
--
--   $white*$eol                   { \p s -> TokenNL p }
--   $eol+                         { \p s -> TokenNL p }
--   $white+                       ;
--   "--".*                        ;
--   "{-" (\\.|[^\{\-]|\n)* "-}"   ;
--   import$white+@importFilePath  { \p s -> TokenImport p s }
--   @constr                       { \p s -> TokenConstr p s }
--   forall                        { \p s -> TokenForall p }
--   ∀                             { \p s -> TokenForall p }
--   let                           { \p s -> TokenLet p }
--   data                          { \p s -> TokenData p }
--   where                         { \p s -> TokenWhere p }
--   module                        { \p s -> TokenModule p }
--   hiding                        { \p s -> TokenHiding p }
--   in                            { \p s -> TokenIn p }
--   if                            { \p s -> TokenIf p }
--   then                          { \p s -> TokenThen p }
--   else                          { \p s -> TokenElse p }
--   case                          { \p s -> TokenCase p }
--   of                            { \p s -> TokenOf p }
--   ∞                             { \p s -> TokenInfinity p }
--   @float                        { \p s -> TokenFloat p s }
--   @int                          { \p s -> TokenInt p $ read s }
--   @charLiteral                  { \p s -> TokenCharLiteral p $ read s }
--   @stringLiteral                { \p s -> TokenStringLiteral p $ read s }
--   "->"                          { \p s -> TokenArrow p }
--   "→"                           { \p s -> TokenArrow p }
--   "<-"                          { \p s -> TokenBind p }
--   "←"                           { \p s -> TokenBind p }
--   \;                            { \p s -> TokenSemicolon p }
--   \=                            { \p s -> TokenEq p }
--   "/="                          { \p s -> TokenNeq p }
--   "≠"                           { \p _ -> TokenNeq p }
--   \\                            { \p s -> TokenLambda p }
--   "λ"                           { \p s -> TokenLambda p }
--   \[                            { \p s -> TokenBoxLeft p }
--   \]                            { \p s -> TokenBoxRight p }
--   [\+]                          { \p s -> TokenAdd p }
--   [\-]                          { \p s -> TokenSub p }
--   [\*]                          { \p s -> TokenMul p }
--   \(                            { \p s -> TokenLParen p }
--   \)                            { \p s -> TokenRParen p }
--   \{                            { \p s -> TokenLBrace p }
--   \}                            { \p s -> TokenRBrace p }
--   \<                            { \p s -> TokenLangle p }
--   \>                            { \p s -> TokenRangle p }
--   \,                            { \p s -> TokenComma p }
--   \×                            { \p s -> TokenCross p }
--   \.                            { \p s -> TokenPeriod p }
--   \:                            { \p s -> TokenSig p }
--   @sym				                  { \p s -> TokenSym p s }
--   \_                            { \p _ -> TokenUnderscore p }
--   \|                            { \p s -> TokenPipe p }
--   \/                            { \p s -> TokenForwardSlash p }
--   "≤"                           { \p s -> TokenLesserEq p }
--   "<="                          { \p s -> TokenLesserEq p }
--   "≥"                           { \p s -> TokenGreaterEq p }
--   ">="                          { \p s -> TokenGreaterEq p }
--   "=="                          { \p s -> TokenEquiv p }
--   "≡"                           { \p s -> TokenEquiv p }
--   "`"                           { \p s -> TokenBackTick p }
--   "^"                           { \p s -> TokenCaret p }
--   ".."                          { \p s -> TokenDotDot p }
--   "∨"                           { \p _ -> TokenJoin p }
--   "\\/"                         { \p _ -> TokenJoin p }
--   "∧"                           { \p _ -> TokenMeet p }
--   "/\\"                         { \p _ -> TokenMeet p }
--   "=>"                          { \p s -> TokenConstrain p }
--   "⇒"                           { \p s -> TokenConstrain p }
--   "∘"                           { \p _ -> TokenRing p }
--   "?"                           { \p _ -> TokenEmptyHole p }
--   "{!"                          { \p _ -> TokenHoleStart p }
--   "!}"                          { \p _ -> TokenHoleEnd p}
--
-- {
--
-- data Token
--   = TokenLet    AlexPosn
--   | TokenIn     AlexPosn
--   | TokenIf     AlexPosn
--   | TokenThen   AlexPosn
--   | TokenElse   AlexPosn
--   | TokenData   AlexPosn
--   | TokenTypeDecl AlexPosn
--   | TokenWhere  AlexPosn
--   | TokenModule AlexPosn
--   | TokenHiding AlexPosn
--   | TokenCase   AlexPosn
--   | TokenOf     AlexPosn
--   | TokenInfinity AlexPosn
--   | TokenLambda AlexPosn
--   | TokenLetBox AlexPosn
--   | TokenBind   AlexPosn
--   | TokenBox    AlexPosn
--   | TokenInt    AlexPosn Int
--   | TokenFloat  AlexPosn String
--   | TokenSym    AlexPosn String
--   | TokenArrow  AlexPosn
--   | TokenConstrain AlexPosn
--   | TokenForall AlexPosn
--   | TokenEq     AlexPosn
--   | TokenNeq     AlexPosn
--   | TokenAdd    AlexPosn
--   | TokenSub    AlexPosn
--   | TokenMul    AlexPosn
--   | TokenCharLiteral AlexPosn Char
--   | TokenStringLiteral AlexPosn Text
--   | TokenLParen AlexPosn
--   | TokenRParen AlexPosn
--   | TokenNL     AlexPosn
--   | TokenConstr AlexPosn String
--   | TokenBackTick AlexPosn
--   | TokenSig    AlexPosn
--   | TokenBoxLeft AlexPosn
--   | TokenBoxRight AlexPosn
--   | TokenLBrace   AlexPosn
--   | TokenRBrace   AlexPosn
--   | TokenLangle   AlexPosn
--   | TokenRangle   AlexPosn
--   | TokenComma    AlexPosn
--   | TokenCross AlexPosn
--   | TokenPeriod   AlexPosn
--   | TokenPipe     AlexPosn
--   | TokenUnderscore AlexPosn
--   | TokenSemicolon  AlexPosn
--   | TokenForwardSlash AlexPosn
--   | TokenLesserEq AlexPosn
--   | TokenGreaterEq AlexPosn
--   | TokenEquiv AlexPosn
--   | TokenCaret AlexPosn
--   | TokenDotDot AlexPosn
--   | TokenJoin AlexPosn
--   | TokenMeet AlexPosn
--   | TokenRing AlexPosn
--   | TokenImport AlexPosn String
--   | TokenEmptyHole AlexPosn
--   | TokenHoleStart AlexPosn
--   | TokenHoleEnd AlexPosn
--
--   deriving (Eq, Show, Generic)
--
-- symString :: Token -> String
-- symString (TokenSym _ x) = x
--
-- constrString :: Token -> String
-- constrString (TokenConstr _ x) = x
--
-- scanTokens = alexScanTokens >>= (return . trim)
--
-- trim :: [Token] -> [Token]
-- trim = reverse . trimNL . reverse . trimNL
--
-- trimNL :: [Token] -> [Token]
-- trimNL [] = []
-- trimNL (TokenNL _ : ts) = trimNL ts
-- trimNL ts = ts
--
-- instance FirstParameter Token AlexPosn
--
-- getPos :: Token -> (Int, Int)
-- getPos t = (l, c)
--   where (AlexPn _ l c) = getFirstParameter t
--
-- getPosToSpan :: Token -> ((Int, Int), (Int, Int))
-- getPosToSpan t = (getPos t, getPos t)
--
-- }

-- {-| The lexer is generated by Alex (<http://www.haskell.org/alex>) and is an
--     adaptation of GHC's lexer. The main lexing function 'lexer' is called by
--     the "Language.Granule.Syntax.Parser.Parser" to get the next token from the input.
-- -}
--
{
module Language.Granule.Syntax.Lexer
  ( lexer
    -- * Lex states
  , normal, code
  , layout, empty_layout, bol, imp_dir
    -- * Alex generated functions
  , AlexReturn(..), alexScanUser
  ) where


import Language.Granule.Syntax.Literal
import Language.Granule.Syntax.Parser.Alex
import Language.Granule.Syntax.Parser.Comments
import {-# SOURCE #-} Language.Granule.Syntax.Parser.Layout
import {-# SOURCE #-} Language.Granule.Syntax.Parser.LexActions
import Language.Granule.Syntax.Parser.Monad
import Language.Granule.Syntax.Parser.Tokens

}

-- Unicode is not handled by the following regular expressions.
-- Instead, unicode characters are translated to 7-bit ASCII
-- by Language.Granule.Syntax.Parser.LexActions.foolAlex in a preprocessing pass.

$digit       = 0-9
$hexdigit    = [ $digit a-f A-F ]
-- $alpha       = [ A-Z a-z _ ]
$alpha  = [a-zA-Z\_\-\=]
-- $op          = [ \- \! \# \$ \% \& \* \+ \/ \< \= \> \^ \| \~ \? \` \[ \] \, \: ]
-- $idstart     = [ $digit $alpha $op ]
-- $idchar      = [ $idstart ' \\ ]
-- $nonalpha    = $idchar # $alpha
$white_notab = $white # \t
$white_nonl  = $white_notab # \n

@number       = $digit+ | "0x" $hexdigit+
@prettynumber = $digit+ ([_] $digit+)* | "0x" $hexdigit+
@integer      = [\-]? @prettynumber
-- @exponent     = [eE] [\-\+]? @number
-- @float        = @integer \. @number @exponent? | @number @exponent

$letter = [a-zA-Z]
-- $eol    = [\n]
$alphanum  = [$alpha $digit \_]
@ident      = $letter ($alphanum | \')*
@q_ident    = (@ident \.)* @ident

-- A name can't start with \x (to allow \x -> x).
-- Bug in alex: [ _ op ]+ doesn't seem to work!
-- AGDA names below
-- @start = ($idstart # [_]) | \\ [ $nonalpha ]
-- @ident = @start $idchar* | [_] $idchar+

-- @namespace  = (@ident \.)*
-- @q_ident    = @namespace @ident

tokens :-

-- White space
<0,code,bol_,layout_,empty_layout_,imp_dir_>
    $white_nonl+    ;

<pragma_,fpragma_> $white_notab ;

-- Comments
    -- We need to rule out pragmas here. Usually longest match would take
    -- precedence, but in some states pragmas aren't valid but comments are.
<0,code,bol_,layout_,empty_layout_,imp_dir_>
    "{-" / { not' (followedBy '#') }    { nestedComment }
    -- A misplaced end-comment, like in @f {x-} = x-@ gives a parse error.
    "-}"                                { symbol SymEndComment }
    @ident "-}"                         { symbol SymEndComment }

-- Dashes followed by a name symbol should be parsed as a name.
<0,code,bol_,layout_,empty_layout_,imp_dir_>
   "--" .* / { keepComments .&&. (followedBy '\n' .||. eof) }
             { withInterval TokComment }
<0,code,bol_,layout_,empty_layout_,imp_dir_>
  "--" .* / { followedBy '\n' .||. eof } ;

-- We need to check the offside rule for the first token on each line.  We
-- should not check the offside rule for the end of file token or an
-- '\end{code}'
<0,code,imp_dir_> \n    { begin bol_ }
<bol_>
    {
        \n                  ;
--      ^ \\ "end{code}"    { end }
        () / { not' eof }       { offsideRule }
    }

-- After a layout keyword there is either an open brace (no layout) or the
-- indentation of the first token decides the column of the layout block.
<layout_>
    {   \n      ;
--      \{      { endWith openBrace }
        ()      { endWith newLayoutContext }
    }

-- The only rule for the empty_layout state. Generates a close brace.
<empty_layout_> ()              { emptyLayout }

-- Keywords
<0,code> forall         { keyword KwForall }
<0,code> ∀              { keyword KwForall }
<0,code> let            { keyword KwLet }
<0,code> data           { keyword KwData }
<0,code> where          { keyword KwWhere }
<0,code> module         { keyword KwModule }
<0,code> hiding         { keyword KwHiding }
<0,code> in             { keyword KwIn }
<0,code> if             { keyword KwIf }
<0,code> then           { keyword KwThen }
<0,code> else           { keyword KwElse }
<0,code> case           { keyword KwCase }
<0,code> of             { keyword KwOf }

-- Holes
<0,code> "{!"           { hole }

-- Special symbols
<0,code> "."            { symbol SymDot }
<0,code> ","            { symbol SymComma }
<0,code> ";"            { symbol SymSemi }
<0,code> "::"           { symbol SymDoubleColon }
<0,code> ":"            { symbol SymColon }
<0,code> "="            { symbol SymEqual }
<0,code> "_"            { symbol SymUnderscore }
<0,code> "?"            { symbol SymQuestionMark }
<0,code> "|"            { symbol SymBar }
<0,code> "("            { symbol SymOpenParen }
<0,code> ")"            { symbol SymCloseParen }
<0,code> "["            { symbol SymOpenBracket }
<0,code> "]"            { symbol SymCloseBracket }
<0,code> "()"           { symbol SymAbsurd }
<0,code> "->"           { symbol SymArrow }
<0,code> "*"            { symbol SymStar }
<0,code> "+"            { symbol SymPlus }
<0,code> "@"            { symbol SymAt }
<0,code> "\"            { symbol SymLambda } -- "
<0,code> "{"            { symbol SymOpenBrace }     -- you can't use braces for layout
<0,code> "}"            { symbol SymCloseBrace }

-- Literals
<0,code> @integer       { literal' integer LitNat }

-- Identifiers
<0,code,imp_dir_> @q_ident      { identifier }
-- Andreas, 2013-02-21, added identifiers to the 'imp_dir_' state.
-- This is to fix issue 782: 'toz' should not be lexed as 'to'
-- (followed by 'z' after leaving imp_dir_).
-- With identifiers in state imp_dir_, 'toz' should be lexed as
-- identifier 'toz' in imp_dir_ state, leading to a parse error later.

{

-- | This is the initial state for parsing a regular, non-literate file.
normal :: LexState
normal = 0


{-| The layout state. Entered when we see a layout keyword ('withLayout') and
    exited either when seeing an open brace ('openBrace') or at the next token
    ('newLayoutContext').

    Update: we don't use braces for layout anymore.
-}
layout :: LexState
layout = layout_


{-| The state inside a pragma.
-}
pragma :: LexState
pragma = pragma_

-- | The state inside a FOREIGN pragma. This needs to be different so that we don't
--   lex further strings as pragma keywords.
fpragma :: LexState
fpragma = fpragma_

{-| We enter this state from 'newLayoutContext' when the token following a
    layout keyword is to the left of (or at the same column as) the current
    layout context. Example:

    > data Empty : Set where
    > foo : Empty -> Nat

    Here the second line is not part of the @where@ clause since it is has the
    same indentation as the @data@ definition. What we have to do is insert an
    empty layout block @{}@ after the @where@. The only thing that can happen
    in this state is that 'emptyLayout' is executed, generating the closing
    brace. The open brace is generated when entering by 'newLayoutContext'.
-}
empty_layout :: LexState
empty_layout = empty_layout_


-- | This state is entered at the beginning of each line. You can't lex
--   anything in this state, and to exit you have to check the layout rule.
--   Done with 'offsideRule'.
bol :: LexState
bol = bol_


-- | This state can only be entered by the parser. In this state you can only
--   lex the keywords @using@, @hiding@, @renaming@ and @to@. Moreover they are
--   only keywords in this particular state. The lexer will never enter this
--   state by itself, that has to be done in the parser.
imp_dir :: LexState
imp_dir = imp_dir_


-- | Return the next token. This is the function used by Happy in the parser.
--
--   @lexer k = 'lexToken' >>= k@
lexer :: (Token -> Parser a) -> Parser a
lexer k = lexToken >>= k

-- | Do not use this function; it sets the 'ParseFlags' to
-- 'undefined'.
alexScan :: AlexInput -> Int -> AlexReturn (LexAction Token)

-- | This is the main lexing function generated by Alex.
alexScanUser :: ([LexState], ParseFlags) -> AlexInput -> Int -> AlexReturn (LexAction Token)

}
