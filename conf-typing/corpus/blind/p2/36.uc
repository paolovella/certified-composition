alloc buf ;
store buf v ;
for i = 3 { emit log "chunk" ; free buf }
