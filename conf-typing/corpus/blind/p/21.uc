alloc res ;
store res qty ;
if inrange {
  emit html "ok" ;
  free res
} else {
  emit html "error_quantity_out_of_range" ;
  free res
}
