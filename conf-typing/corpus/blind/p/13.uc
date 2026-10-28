check cache ;
access cache ;
if hit {
  emit html "cached_value"
} else {
  alloc val ;
  store val computed ;
  access cache ;
  emit html "computed_value" ;
  free val
}
