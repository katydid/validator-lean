# Derivative Algorithm for Validation

This package provides multiple implementations of the derivative algorithm for validation of parse (labelled) trees in an effort to make it more understandable.

 * [LTreeOriginal](./LTreeOriginal.lean) is based on the original regular expression derivative algorithm and extends it to parse trees by swapping the character operator for a tree node operator. NO compression, NO monads, NO parser, NOT memoizable, NO memoization.
 * [LTreeVerbose](./LTreeVerbose.lean) is the simplest version of the memoizable algorithm, which using [enter](./Enter.lean) and [leave](./LeaveVerbose.lean). NO compression, NO monads, NO parser. NO memoization.
 * [LTreeVerboseCompress](./LTreeConciseCompress.lean) adds compression to [LTreeVerbose](./LTreeVerbose.lean) for a little extra efficiency. NO monads, NO parser, NO memoization.
 * [LTreeConcise](./LTreeConcise.lean) is the simplest version of the memoizable algorithm, which using [enter](./Enter.lean) and [leave](./Leave.lean). It uses monads to make the code more concise. NO compression, NO parser, NO memoization.
 * [LTreeConciseCompress](./LTreeConciseCompress.lean) adds compression to [LTreeConcise](./LTreeConcise.lean) for a little extra efficiency. NO parser, NO memoization.
 * [ParserConcise](./ParserConcise.lean) is the simplest version of the memoizable algorithm that uses a parser. NO compression, NO memoization.
 * [ParserConciseCompress](./ParserConciseCompress.lean) adds compression to [ParserConcise](./ParserConcise.lean) for a little extra efficiency. NO memoization.
 * [ParserConciseMem](./ParserConciseMem.lean) is the simplest version of the memoized algorithm that uses a parser. NO compression.
 * [ParserConciseCompressMem](./ParserConciseCompressMem.lean) adds compression to [ParserConciseMem](./ParserConciseMem.lean) for a little extra efficiency.