alloc conn ;
check db ;
access db ;
if err { emit log "query_failed" } else { deref conn ; emit html "result" } ;
free conn
