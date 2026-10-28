check doc ;
let ok = authorized ;
if ok { access doc ; emit html "doc" } else { emit html "denied" }
