alloc buf ;
let z = 0 ;
store buf z ;
for i = 10 { load cur buf ; let cur = ( cur + chunk ) ; store buf cur } ;
deref buf ;
emit html "response" ;
free buf
