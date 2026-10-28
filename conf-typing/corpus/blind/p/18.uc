if flag {
  alloc scratch ;
  store scratch v
} else {
  skip
} ;
emit html "done" ;
if flag {
  free scratch
} else {
  skip
}
