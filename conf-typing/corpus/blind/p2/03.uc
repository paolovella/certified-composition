alloc buf ;
let code = 200 ;
store buf code ;
if err { emit html "error" } else { deref buf ; emit html "ok" } ;
free buf
