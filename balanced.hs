data F a = F0 a | F1 (F (G a))

data G a = G0 a | G1 a (G a)

main = do
  print "type checks"
