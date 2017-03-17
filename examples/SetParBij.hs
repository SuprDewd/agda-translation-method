import SetParData (pairing)
import Data.List
import Data.Maybe

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
         (q, [])   -> insertMax m i (bij q)
         (q, [[]]) -> bij q ++ [[m+1]]
