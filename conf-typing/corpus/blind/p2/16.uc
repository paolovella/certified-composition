alloc buf ;
store buf v ;
if fail1 { emit html "error_step1" } else { if fail2 { emit html "error_step2" } else { deref buf ; emit html "ok" } } ;
free buf
