(((address 0x1E)
 (invariant
   "(assert
      (let ((x ((_ zero_extend 32) ((_ extract 31 0) RDI)))
            (y ((_ zero_extend 32) ((_ extract 31 0) RSI))))
      (and (= (bvadd x y) #x0000000000000005)
           (bvule x #x0000000000000005)
           (bvuge y #x0000000000000000))))")))
