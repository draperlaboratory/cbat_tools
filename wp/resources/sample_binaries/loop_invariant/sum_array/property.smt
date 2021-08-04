(define-fun-rec sum_array ((start (_ BitVec 64)) (end (_ BitVec 64)))
                           (_ BitVec 8)
  (ite (= start end)
       #x00
       (bvadd (select mem start)
              (sum_array (bvadd start #x0000000000000001) end)))
)
(assert
  (let  ((length  ((_ zero_extend 56) ((_ extract 7 0) init_RDI)))
         (array   init_RSI))
  (= RAX ((_ zero_extend 56) (sum_array array (bvadd array length))))))


