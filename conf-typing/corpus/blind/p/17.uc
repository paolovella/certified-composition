for i = 8 {
  alloc conn ;
  store conn open ;
  load st conn ;
  if st {
    emit log "closing_connection"
  } else {
    skip
  } ;
  free conn
}
