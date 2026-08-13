alloc ptr ; if err { let abrt = 1 } else { skip } ; if abrt { deref ptr } else { skip } ; free ptr
