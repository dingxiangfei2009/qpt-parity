import Control.Monad
import Control.Applicative hiding (many)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List

import Text.Parsec hiding (Empty)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.String
import Text.Parsec.Token

import System.Environment

data Owner = Even | Odd deriving (Show, Eq)

data Colour a = Colour a | Empty deriving (Eq)
instance Show a => Show (Colour a) where
  show Empty = "_"
  show (Colour x) = show x

data Vertex a b =
  Vertex {
  vertexId :: a,
  vertexColour :: Colour b,
  owner :: Owner,
  vertexSuccessors :: [a]
  } deriving (Show)

data Graph a b =
  Graph {
  vertices :: Map.Map a (Vertex a b)
  } deriving (Show)

instance Integral a => Ord (Colour a) where
  Empty <= _ = True
  Colour _ <= Empty = False
  Colour x <= Colour y =
    if even x then
      even y && x <= y
    else
      even y || x >= y

isEvenColour :: Integral a => Colour a -> Bool
isEvenColour (Colour c) = even c
isEvenColour Empty = False

colourOwner :: Integral a => Colour a -> Owner
colourOwner (Colour x) =
  if even x then
    Even
  else
    Odd

sortAndRemoveDuplicate :: Ord a => [a] -> [a]
sortAndRemoveDuplicate = map head . group . sort

type SuccessorMap a = Map.Map (Colour a) (Colour a)
type Witness a = [Colour a]

compareWitness :: Integral a => Witness a -> Witness a -> Ordering
compareWitness [] [] = EQ
compareWitness (a:as) (b:bs) =
  case compareWitness as bs of
    EQ -> compare a b
    x -> x

maxWitness :: Integral a => Witness a -> Witness a -> Witness a
maxWitness a b =
  case compareWitness a b of
    LT -> b
    _ -> a

value :: Integral a => Witness a -> Int
value =
  fst .
    foldl'
      (\(sum, exp) c -> (sum + value' c exp, exp * 2))
      (0, 1)
  where
    value' (Colour c') exp | even c' = exp
    value' _ _ = 0

makeColourSuccessors :: Integral a => [Colour a] -> SuccessorMap a
makeColourSuccessors cs =
  let
    makeSuccessorPairs =
      foldl
        (\(prev, cs) c -> (c, (prev, c):cs))
        (Empty, [])
    (_, cs') = makeSuccessorPairs $ sortAndRemoveDuplicate cs
  in
    Map.fromList cs'

firstNonEmpty :: Witness a -> Maybe (Colour a)
firstNonEmpty =
  find $
  \x -> case x of
    Empty -> False
    _ -> True

stillMonotonic :: Integral a => a -> Witness a -> Bool
stillMonotonic x =
  (maybe True $ \(Colour x') -> x' >= x) . firstNonEmpty

positionUpdatedByConcatenation :: Integral a =>
  Witness a -> a -> Maybe Int
positionUpdatedByConcatenation cs x =
  search cs x 0
  where
    goodPosition x cs pos =
      if stillMonotonic x cs then
        Just pos
      else
        Nothing
    search [] _ _ = Nothing
    search [Colour _] _ pos = Just pos
    search (Empty : cs) x pos = goodPosition x cs pos
    search ((Colour x') : cs) x pos =
      {- look ahead -}
      if odd x' then
        goodPosition x cs pos
      else
        search cs x (pos + 1)

positionUpdatedBySubstitution :: Integral a =>
  Witness a -> a -> Maybe Int
positionUpdatedBySubstitution cs x =
  search cs x 0
  where
    search [] _ _ = Nothing
    search (Empty : cs) x pos = search cs x (pos + 1)
    search (Colour x' : cs) x pos =
      if x > x' && stillMonotonic x cs then
        Just pos
      else
        search cs x (pos + 1)

update :: Integral a =>
  Int -> a -> Witness a -> Witness a
update pos c cs =
  case cs of
    [] -> []
    c' : cs ->
      if pos > 0 then
        Empty : (update (pos - 1) c cs)
      else
        (Colour c) : cs

basicUpdate :: Integral a =>
  a -> Witness a -> Witness a
basicUpdate c cs =
  let
    pos = positionUpdatedBySubstitution cs c
    pos' = positionUpdatedByConcatenation cs c
  in
    case max pos pos' of
      Nothing -> cs
      Just pos -> update pos c cs

antagonistUpdate :: Integral a =>
  SuccessorMap a -> a -> Witness a -> Witness a
antagonistUpdate succ c cs =
  case positionUpdatedBySubstitution cs c of
    Nothing ->
      case positionUpdatedByConcatenation cs c of
        Nothing ->
          cs
        Just pos ->
          {- antagonist -}
          maxWitness
            (update pos c cs)
            (basicUpdate c (immediateSucc succ cs))
    Just pos ->
      case positionUpdatedByConcatenation cs c of
        Nothing ->
          update pos c cs
        Just pos' ->
          if pos < pos' then
            {- antagonist -}
            maxWitness
              (update pos' c cs)
              (basicUpdate c (immediateSucc succ cs))
          else
            update pos c cs

immediateSucc :: Integral a =>
  SuccessorMap a -> Witness a -> Witness a
immediateSucc succ b@(c : cs) =
  bump (Left [put Empty]) cs
  where
    put = (:)
    bump (Left _) [] = b
    bump (Right ps) [] = foldr (flip (.)) id ps []
    bump (Left ps) (c:cs) =
      bump
        (
          case succ Map.!? c of
            Nothing ->
              Left $ (put Empty):ps
            Just (Colour c') ->
              if stillMonotonic c' cs then
                Right $ put (Colour c'):ps
              else
                Left $ (put Empty):ps
        )
        cs
    bump (Right ps) (c:cs) =
      bump (Right $ (put c):ps) cs

data VertexState a = Won | Progress (Witness a)
  deriving (Show, Eq)

instance Integral a => Ord (VertexState a) where
  Won <= Won = True
  Won <= _ = False
  _ <= Won = True
  Progress a <= Progress b = reverse a <= reverse b

type SolveState a b = Map.Map a (VertexState b)

-- logarithm helper
integerLog2 :: Integral a => a -> Int
integerLog2 n =
  itr n 0
  where
    itr n c | n > 1 = itr (n `div` 2) (c + 1)
    itr _ c = c

solve :: (Ord a, Integral b) =>
  Graph a b -> Integer -> SolveState a b
solve game limit =
  valueIteration initial (Set.fromList vids) limit
  where
    vs = vertices game
    vids = foldMap ((: []) . vertexId) vs
    reverseLookup =
      fmap Set.fromList $
      foldr
        (\ v rev ->
          foldr
            (\ succ rev -> Map.adjust (\ s -> (vertexId v) : s) succ rev)
            rev
            (vertexSuccessors v)
        )
        (Map.fromList $ zip vids $ replicate (length vids) [])
        vs
    colours = foldMap ((: []) . vertexColour) vs
    evenColourCount =
      length . filter isEvenColour . sortAndRemoveDuplicate $
        colours
    succ = makeColourSuccessors colours
    witnessLength = 2 + (integerLog2 (toInteger evenColourCount))
    initial =
      fmap (const . Progress $ replicate witnessLength Empty) vs

    valueIteration curr updating cnt =
      let
        (updating', next) = foldl' (update curr) (Set.fromList [],[]) updating
      in
        if not(null updating') && cnt /= 0 then
          valueIteration
            (Map.union (Map.fromList next) curr)
            updating'
            (cnt - 1)
        else
          curr

    update curr (updating, ss) v =
      let
        oldState = curr Map.! v
        node = vs Map.! v
        result =
          map
            (progress $ vertexColour node)
            (map (curr Map.!) $ vertexSuccessors node)
        op = case owner node of
          Even -> maximum
          Odd -> minimum
        newState = op result
      in
        if newState <= oldState then
          (updating, (v, oldState) : ss)
        else
          (
            Set.union (reverseLookup Map.! v) updating,
            (v, newState) : ss
          ) -- liftable

    progress _ Won = Won
    progress (Colour c) (Progress cs) =
      if (value cs') > evenColourCount then
        Won
      else
        Progress cs'
      where
        cs' = antagonistUpdate succ c cs

-- pqsolver GM parser

digits = many1 digit

nonprint = oneOf " \n\r\t"

parseHeader :: Parser Int
parseHeader = do
  string "parity"
  skipMany1 nonprint
  n <- liftM read $ digits
  skipMany nonprint
  char ';'
  return n

parseItem :: Parser (Vertex Int Int)
parseItem = do
  skipMany nonprint
  vertexId <- liftM read $ digits
  skipMany1 nonprint
  colour <- liftM read $ digits
  skipMany1 nonprint
  owner <- liftM read $ digits
  skipMany1 nonprint
  successors <- liftM (fmap read) $
    sepBy digits (char ',')
  skipMany $ noneOf ";"
  char ';'
  skipMany nonprint
  return $ Vertex {
    vertexId=vertexId,
    vertexColour=Colour colour,
    owner=if owner == 0 then Even else Odd,
    vertexSuccessors=successors
  }

parseFile :: Parser (Graph Int Int)
parseFile = do
  n <- parseHeader
  vs <- liftM (fmap (\ v -> (vertexId v, v))) $ count n parseItem
  return $ Graph {vertices=Map.fromList vs}

parseGame :: String -> Either ParseError (Graph Int Int)
parseGame = parse parseFile "(parity)"

-- Trivial Main

getIterations :: [String] -> Integer
getIterations [] = -1
getIterations (iterationStr : _) = read iterationStr :: Integer

main = do
  args <- getArgs
  let iterations = getIterations args
  gameDescription <- getContents
  let game = parseGame gameDescription
  case game of
    Left error ->
      putStrLn . show $ error
    Right game -> do
      let result = solve game iterations
      putStrLn "Result:"
      putStrLn . show $ result
      putStrLn "Summary:"
      putStrLn "Even winning region"
      let (evens, odds) = partition
                          (\(_, s) -> s == Won)
                          (Map.toList result)
      putStrLn . show . map fst $ evens
      putStrLn "Odd winning region"
      putStrLn . show . map fst $ odds
