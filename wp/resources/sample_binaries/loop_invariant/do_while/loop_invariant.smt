(((address 0x12)
 (invariant
   "(define-fun read ((addr (_ BitVec 64))) (_ BitVec 32)
      (concat (select mem (bvadd addr #x0000000000000003))
              (select mem (bvadd addr #x0000000000000002))
              (select mem (bvadd addr #x0000000000000001))
              (select mem addr)))
    (assert
      (let ((x (read (bvsub RBP #x0000000000000004)))
            (y (read (bvsub RBP #x0000000000000008))))
      (and (= (bvadd x y) #x00000005)
           (bvult x #x00000005)
           (bvuge y #x00000000))))")))
