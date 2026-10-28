alloc buf ;
if fits { check msg ; for i = 64 { access msg ; store buf byte } ; emit html "ok" } else { emit html "length_too_large" } ;
free buf
