module Language.Granule.Syntax.Identifiers where

-- | Internal representation of entinames (variables)
-- which pairs their source name string with an internal name
-- which is useually freshly generate. Error messages should
-- always use the 'sourceId', anything involving new name
-- generation should use 'internalId'
data Id = Id { sourceId :: String, internalId :: String }
  deriving (Eq, Ord)

instance Show Id where
  show (Id s i) = "(Id " <> show s <> " " <> show i <> ")"

mkId :: String -> Id
mkId x = Id x x
