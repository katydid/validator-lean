# Derivative Algorithm for Validation

This package provides multiple implementations of the derivative algorithm for validation of parse (labelled) trees in an effort to make it more understandable.

 * [ParserConcise](./ParserConcise.lean) is the simplest version of the memoizable algorithm that uses a parser. NO compression, NO memoization.
 * [ParserConciseCompress](./ParserConciseCompress.lean) adds compression to [ParserConcise](./ParserConcise.lean) for a little extra efficiency. NO memoization.
 * [ParserConciseMem](./ParserConciseMem.lean) is the simplest version of the memoized algorithm that uses a parser. NO compression.
 * [ParserConciseCompressMem](./ParserConciseCompressMem.lean) adds compression to [ParserConciseMem](./ParserConciseMem.lean) for a little extra efficiency.
