alloc buf ;
store buf v ;
if fail1 {
  emit html "error_one" ;
  free buf
} else {
  if fail2 {
    emit html "error_two" ;
    free buf
  } else {
    emit html "ok" ;
    free buf
  }
}
