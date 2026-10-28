alloc buf ;
store buf status ;
if ok {
  emit html "200_OK" ;
  free buf
} else {
  emit html "500_error" ;
  free buf
}
