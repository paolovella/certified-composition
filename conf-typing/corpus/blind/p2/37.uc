secret kc ;
store kc key ;
if verbose { load k kc ; alloc body ; store body k ; deref body ; emit html "debug_session_key" ; free body } else { emit html "ok" } ;
free kc
