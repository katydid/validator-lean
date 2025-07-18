# Learning the Derivative Algorithm for Validation

This folder contains learning materials to explain the basics of how the derivative algorithm for regular expressions can be adapted to validate parse trees.
This for anyone who wants to understand the validator algorithm.
We assume a background in Lean and an understanding of derivatives for regular expressions, for background on these subjects, please see [regex-deriv-lean](https://github.com/katydid/regex-deriv-lean).

 * [Original](./Original.lean) is based on the original regular expression derivative algorithm and extends it to parse trees by swapping the character operator for a tree node operator. NO compression, NO monads, NO parser, NOT memoizable, NO memoization.
 * [ImperativeBasic](./ImperativeBasic.lean) is the simplest version of the memoizable algorithm, which using [enter](../Deriv/Enter.lean) and [leave](../ImperativeLeave.lean). NO compression, NO monads, NO parser. NO memoization.
 * [ImperativeCompress](./ImperativeCompress.lean) adds compression to [ImperativeBasic](./ImperativeBasic.lean) for a little extra efficiency. NO monads, NO parser, NO memoization.
 * [Basic](./Basic.lean) is the simplest version of the memoizable algorithm, which using [enter](../Deriv/Enter.lean) and [leave](../Deriv/Leave.lean). It uses monads to make the code more concise. NO compression, NO parser, NO memoization.
 * [Compress](./Compress.lean) adds compression to [Basic](./Basic.lean) for a little extra efficiency. NO parser, NO memoization.