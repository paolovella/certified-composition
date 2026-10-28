secret keycell ;
store keycell key ;
if role {
  check admin ;
  access admin ;
  emit html "granted"
} else {
  emit html "denied"
} ;
free keycell
