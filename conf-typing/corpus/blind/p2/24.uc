alloc buf ;
for i = 16 { if more { store buf byte } else { skip } } ;
deref buf ;
emit html "copied" ;
free buf
