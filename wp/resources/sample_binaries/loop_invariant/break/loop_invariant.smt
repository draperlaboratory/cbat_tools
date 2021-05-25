(((address 0x1e)
 (invariant
   "(define-fun read ((addr (_ BitVec 64))) (_ BitVec 32)
      (concat (select mem (bvadd addr #x0000000000000003))
              (select mem (bvadd addr #x0000000000000002))
              (select mem (bvadd addr #x0000000000000001))
              (select mem addr)))
    (assert
      (let ((j (read (bvsub RBP #x0000000000000004)))
            (i (read (bvsub RBP #x0000000000000008))))
      (and (bvule i #x00000003)
           (= j #x00000005))))")))
