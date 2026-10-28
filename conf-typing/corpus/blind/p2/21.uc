alloc buf ;
check inventory ;
access inventory ;
if inrange { store buf qty ; emit html "ok" } else { emit html "error_quantity_out_of_range" } ;
free buf
