import Validator.Parser.Token

-- ParseTree is a Labelled Tree.
inductive ParseTree where
  | mk (label: Token) (children: List ParseTree)

namespace ParseTree

def node (s: String) (children: List ParseTree): ParseTree :=
  ParseTree.mk (Token.string s) children

def str (s: String): ParseTree :=
  ParseTree.mk (Token.string s) []

def getLabel (t: ParseTree): Token :=
  match t with
  | ParseTree.mk l _ => l

def getChildren (t: ParseTree): List ParseTree :=
  match t with
  | ParseTree.mk _ c => c
