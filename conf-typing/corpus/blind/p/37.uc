alloc body ;
if verbose {
  store body key
} else {
  skip
} ;
emit html "response" ;
free body
