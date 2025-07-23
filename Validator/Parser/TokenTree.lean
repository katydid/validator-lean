import Validator.Parser.ParseTree
import Validator.Parser.Token

abbrev TokenTree := ParseTree Token

abbrev TokenForest := ParseForest Token

def TokenTree.mk (t: Token) (children: TokenForest): TokenTree :=
  ParseTree.mk t children

namespace TokenTree

def node (s: String) (children: TokenForest): TokenTree :=
  ParseTree.mk (Token.string s) children

def str (s: String): TokenTree :=
  ParseTree.mk (Token.string s) []
