import SetParData (pairing)
import Data.List
import Data.Maybe
import Control.Monad

type Par = [[Int]]

-- This is the derived / natural bijection
bij :: Par -> Par
bij par = fromMaybe err (lookup par (pairing !! n))
  where
    n = sum (map length par)
    err = error "Not in the domain of the bijection"

remove :: Eq a => a -> [[a]] -> Maybe (Int, [[a]])
remove x = remove' 0
  where
    remove' _ [] = Nothing
    remove' i (xs:xss)
        | x `elem` xs = Just (i, (xs \\ [x]) : xss)
        | otherwise   = (\(i', yss) -> (i', xs : yss)) <$> remove' (i+1) xss

-- Remove the largest element from a set partition. Return the resulting
-- set partition, the maximum, and the index of the block from which the
-- maximum was removed, counting from the right/end of the list.
removeMax :: Par -> (Int, Int, Par)
removeMax par = (m, i, reverse par')
  where
    m = maximum $ map maximum par
    Just (i, par') = remove m (reverse par)

-- Insert a new maximum (m+1) at position i counting from the right and
-- disregarding the block that m belongs to.
insertMax :: Int -> Int -> Par -> Par
insertMax m i par = reverse $ ins i (reverse par)
  where
    ins _ [] = error "Oops, something went wrong"
    ins i (xs : xss)
        = if m `elem` xs
          then xs : ins i xss
          else if i == 0
               then (xs ++ [m+1]) : xss
               else xs : ins (i-1) xss

-- Direct implementation of bij
direct :: Par -> Par
direct []  = [[1]]
direct par =
    let (m, i, p) = removeMax par
    in case break null p of
         (q, [])   -> insertMax m i (direct q)
         (q, [[]]) -> direct q ++ [[m+1]]


-- Direct implementation of bij
direct2 :: Par -> (Par, [Int])
direct2 []  = ([[1]], [0])
direct2 par =
    let (m, i, p) = removeMax par
    in case break null p of
         (q, [])   -> let (q', xs) = direct2 q
                      in (insertMax m i q', xs ++ [i+1])
         (q, [[]]) -> let (q', xs) = direct2 q
                      in (q' ++ [[m+1]], xs ++ [0])

code :: Par -> [Int]
code [] = []
code par =
    let (_, i, p) = removeMax par
    in case break null p of
         (q, [])   -> let xs = code q in xs ++ [i+1]
         (q, [[]]) -> let xs = code q in xs ++ [0]

code' :: Par -> [Int]
code' = snd . direct2

testBijConj1 :: Par -> Bool
testBijConj1 par = 0:code par == code' par

showPar :: Par -> String
showPar = intercalate "-" . map (concatMap show)

showParPair :: (Par, Par) -> String
showParPair (p, q) = showPar p ++ " -> " ++ showPar q

printBij :: Int -> IO ()
printBij = mapM_ (putStrLn . showParPair) . (pairing !!)

zeros :: [Int] -> Int
zeros = length . filter (==0)

codes :: Int -> [[Int]]
codes 0 = [[]]
codes n = [ xs ++ [x] | xs <- codes (n-1), x <- [0 .. zeros xs] ]

-- TODO: Look at the bijection give by Stanley: problem 108 in EC1 2nd ed
-- (and it solution on p. 192). It's not the same as ours, e.g.
-- We:       1456-2378 -> 157-2469-38
-- Stanley:  1456-2378 -> 146-38-2579

main = printBij 8
