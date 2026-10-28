check doc ;
if granted {
  access doc ;
  emit html "document"
} else {
  emit html "403_denied"
}
