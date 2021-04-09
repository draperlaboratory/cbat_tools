(((address 0x12:64u)
 (invariant
   "(assert
      (let ((x!1 (concat (select mem (bvadd #xffffffffffffffff RBP))
                         (select mem (bvadd #xfffffffffffffffe RBP))
                         (select mem (bvadd #xfffffffffffffffd RBP))
                         (select mem (bvadd #xfffffffffffffffc RBP))))
            (y!1 (concat (select mem (bvadd #xfffffffffffffffb RBP))
                         (select mem (bvadd #xfffffffffffffffa RBP))
                         (select mem (bvadd #xfffffffffffffff9 RBP))
                         (select mem (bvadd #xfffffffffffffff8 RBP)))))
      (and (= (bvadd x!1 y!1) #x00000005)
           (bvuge y!1 #x00000000)
           (bvule x!1 #x00000005))))")))
