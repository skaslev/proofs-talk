fix :: (a -> a) -> a
fix f = f (fix f)

fact' :: (Int -> Int) -> Int -> Int
fact' f n = if n == 0 then 1 else n * f (n-1)

fact :: Int -> Int
fact = fix fact'

main = do
  print $ fact 5
