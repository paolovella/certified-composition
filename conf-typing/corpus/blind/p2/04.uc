alloc block ;
for i = 32 { if more { store block row } else { skip } } ;
deref block ;
emit html "records" ;
free block
