secret kc ;
store kc key ;
if role { check admin ; access admin ; emit html "granted" } else { emit html "denied" } ;
free kc
