(((address 0x1D)
 (invariant
   "(assert
      (let ((x ((_ zero_extend 32) ((_ extract 31 0) RDI)))
            (y ((_ zero_extend 32) ((_ extract 31 0) RSI)))
            (z ((_ zero_extend 32) ((_ extract 31 0) RDX))))
      (and (= (bvadd x y) z)
           (bvule x z)
           (bvuge y #x0000000000000000))))")))
