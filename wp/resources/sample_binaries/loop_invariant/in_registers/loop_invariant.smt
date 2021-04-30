(((address 0x1E)
 (invariant
   "(assert
      (let ((x!1 ((_ zero_extend 32) ((_ extract 31 0) RDI)))
            (y!1 ((_ zero_extend 32) ((_ extract 31 0) RSI))))
      (and (= (bvadd x!1 y!1) #x0000000000000005)
           (bvuge y!1 #x0000000000000000)
           (bvule x!1 #x0000000000000005))))")))
