alloc buf ;
let len = 0 ;
for i = 10 {
  let len = ( len + chunk ) ;
  store buf len
} ;
emit html "response" ;
free buf
