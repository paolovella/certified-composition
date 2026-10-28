alloc buf ;
store buf body ;
emit html "response" ;
free buf ;
if err {
  store buf trailer
} else {
  skip
}
