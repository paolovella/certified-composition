check cache ;
access cache ;
if hit { emit html "cached_value" } else { check db ; access db ; alloc v ; store v val ; emit cache "computed_value" ; emit html "computed_value" ; free v }
