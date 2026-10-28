secret tokcell ;
store tokcell token ;
check upstream ;
access upstream ;
emit html "upstream_ok" ;
emit log "upstream_called" ;
free tokcell
