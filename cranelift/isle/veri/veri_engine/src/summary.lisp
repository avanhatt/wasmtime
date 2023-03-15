Counterexample summary
(simplify 
  (bor [ty|64] 
    (band [ty|64] 
      [x|#x1] 
      (iconst [ty|64] (u64_from_imm64 [y|#x0|0b0]))) 
    ([z|#x0|0b0] @ (iconst [ty|64] (u64_from_imm64 [zk|#x0|0b0])))))
=>
(bor [ty|64] [x|#x1|0b1] [z|#x0|0b0])

#x0|0b0 => #x1|0b1

