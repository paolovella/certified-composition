sset method "GET" ;
sset path san ( input ) ;
alloc out ;
store out len ;
deref out ;
emit html ( method ++ ( "_" ++ path ) ) ;
free out
