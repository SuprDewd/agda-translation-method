import SetParData (pairing)
import Data.List
import Data.Maybe

type Par = [[Int]]

-- This is the derived / natural bijection
bij :: Par -> Maybe Par
bij par = let n = sum (map length par) in lookup par (pairing !! n)

remove :: Eq a => a -> [[a]] -> Maybe (Int, [[a]])
remove x = remove' 0
  where
    remove' _ [] = Nothing
    remove' i (xs:xss)
        | x `elem` xs = Just (i, (xs \\ [x]) : xss)
        | otherwise   = (\(i', yss) -> (i', xs : yss)) <$> remove' (i+1) xss

-- Remove the largest element from a set partition. Return the resulting
-- set partition and the index of the block from which the maximum was
-- removed, counting from the right/end of the list.
rmMax :: Par -> (Int, Par)
rmMax par = (i, reverse par')
  where
    m = maximum $ map maximum par
    Just (i, par') = remove m (reverse par)

-- Direct implementation of bij
-- TODO: Incomplete
f :: Par -> (Par, Par, Int)
f par =
    let (i, par') = rmMax par
    in case bij (filter (not . null) par') of
         Nothing    -> error "Not in the domain of the bijection"
         Just par'' -> (par, par'', i)
