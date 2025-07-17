# Derivative Algorithm for Validation

This package provides multiple implementations of the derivative algorithm for validation of parse (labelled) trees in an effort to make it more understandable.

 * [TreeOriginal](./TreeOriginal.lean) is based on the original regular expression derivative algorithm and extends it to parse trees by swapping the character operator for a tree node operator. NO compression, NO monads, NO parser, NOT memoizable, NO memoization.
 * [TreeVerbose](./TreeVerbose.lean) is the simplest version of the memoizable algorithm, which using [enter](./Enter.lean) and [leave](./LeaveVerbose.lean). NO compression, NO monads, NO parser. NO memoization.
 * [TreeVerboseCompress](./TreeConciseCompress.lean) adds compression to [TreeVerbose](./TreeVerbose.lean) for a little extra efficiency. NO monads, NO parser, NO memoization.
 * [TreeConcise](./TreeConcise.lean) is the simplest version of the memoizable algorithm, which using [enter](./Enter.lean) and [leave](./Leave.lean). It uses monads to make the code more concise. NO compression, NO parser, NO memoization.
 * [TreeConciseCompress](./TreeConciseCompress.lean) adds compression to [TreeConcise](./TreeConcise.lean) for a little extra efficiency. NO parser, NO memoization.
 * [ParserConcise](./ParserConcise.lean) is the simplest version of the memoizable algorithm that uses a parser. NO compression, NO memoization.
 * [ParserConciseCompress](./ParserConciseCompress.lean) adds compression to [ParserConcise](./ParserConcise.lean) for a little extra efficiency. NO memoization.
 * [ParserConciseMem](./ParserConciseMem.lean) is the simplest version of the memoized algorithm that uses a parser. NO compression.
 * [ParserConciseCompressMem](./ParserConciseCompressMem.lean) adds compression to [ParserConciseMem](./ParserConciseMem.lean) for a little extra efficiency.