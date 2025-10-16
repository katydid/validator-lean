import Validator.Std.Hedge
import Validator.Parser.Token

abbrev TokenTree := Hedge.Node Token

abbrev TokenForest := Hedge Token

def TokenTree.mk (t: Token) (children: TokenForest): TokenTree :=
  Hedge.Node.mk t children

namespace TokenTree

def node (s: String) (children: TokenForest): TokenTree :=
  Hedge.Node.mk (Token.string s) children

def str (s: String): TokenTree :=
  Hedge.Node.mk (Token.string s) []
