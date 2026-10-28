let total = 0 ;
for r = 4 {
  for c = 6 {
    let total = ( total + count )
  }
} ;
alloc out ;
store out total ;
emit html "aggregated" ;
free out
