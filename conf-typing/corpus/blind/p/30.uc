alloc conn ;
check db ;
access db ;
if err {
  emit log "query_error" ;
  free conn
} else {
  access db ;
  emit html "rows" ;
  free conn
}
