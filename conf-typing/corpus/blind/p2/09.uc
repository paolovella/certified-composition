secret tc ;
store tc token ;
check upstream ;
deref tc ;
access upstream ;
emit html "ok" ;
emit log "upstream_called" ;
free tc
