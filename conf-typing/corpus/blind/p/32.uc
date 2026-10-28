alloc name ;
alloc role ;
alloc quota ;
store name n ;
store role r ;
store quota q ;
if owner {
  check record ;
  access record ;
  store quota newquota
} else {
  skip
} ;
free name ;
free role ;
free quota
