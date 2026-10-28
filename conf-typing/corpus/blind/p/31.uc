check report ;
let ok = 1 ;
if ok {
  access report ;
  emit html "report"
} else {
  emit html "denied"
}
