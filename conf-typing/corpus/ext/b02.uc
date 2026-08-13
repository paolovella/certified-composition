alloc ptr ; if err { let abrt = 1 ; free ptr } else { skip } ; if abrt { deref ptr } else { skip }
