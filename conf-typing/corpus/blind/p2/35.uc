alloc buf ;
store buf v ;
deref buf ;
emit html "response" ;
free buf ;
if err { store buf b } else { skip }
