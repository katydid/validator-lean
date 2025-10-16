import Validator.Capturer.CaptureExpr

namespace CaptureExtract

-- extract extracts a single forest for the whole expression.
-- This based on extractGroups, but only returns one captured forest.
def extract (x: CaptureExpr α): Hedge α :=
  match x with
  | CaptureExpr.emptyset => []
  | CaptureExpr.epsilon => []
  | CaptureExpr.tree _ _ => []
  -- matched returns the matched token and extracts the matched children from the child expression.
  | CaptureExpr.matched tok childExpr => [Hedge.Node.mk tok (extract childExpr)]
  | CaptureExpr.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extract y
    else extract z
  | CaptureExpr.concat y z =>
    extract y ++ extract z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | CaptureExpr.star _ => []
    -- Ignore group, this group will be extracted later by extractGroups.
  | CaptureExpr.group _ y => extract y

-- extractGroups returns the captured forest for each group.
def extractGroups (includePath: Bool) (x: CaptureExpr α): List (Nat × Hedge α) :=
  match x with
  | CaptureExpr.emptyset => []
  | CaptureExpr.epsilon => []
  | CaptureExpr.tree _ _ => []
  -- There may be groups in the childExpr that needs to be extracted.
  | CaptureExpr.matched tok childExpr =>
    if includePath
    then List.map (fun (id, children) => (id, [Hedge.Node.mk tok children])) (extractGroups includePath childExpr)
    else extractGroups includePath childExpr
  | CaptureExpr.or y z =>
    if y.nullable
    then extractGroups includePath y
    else extractGroups includePath z
  | CaptureExpr.concat y z =>
    extractGroups includePath y ++ extractGroups includePath z
  | CaptureExpr.star _ => []
    -- extract the forest for the single group id
  | CaptureExpr.group id y => (id, extract y) :: extractGroups includePath y
