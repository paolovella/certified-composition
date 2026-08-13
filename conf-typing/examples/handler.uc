check db ;
alloc buf ;
for n = 5 {
  access db ;
  alloc t ;
  store t z ;
  emit db ( "'" ++ ( san ( input ) ++ "'" ) ) ;
  free t
} ;
free buf
