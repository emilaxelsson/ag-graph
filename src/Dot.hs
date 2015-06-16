-- | Creating and rendering dot graphs that correspond to expression graphs.
-- Each node has a single output and zero or more inputs.

module Dot where



import Language.Dot  -- cabal install language-dot

-- To generate an SVG file:
--
--     dot -Tsvg file.dot -o file.svg
--
-- Requires `graphviz` to be installed.



-- | Identifier
type ID = Int

-- | Node Label (will be shown in the rendering)
type Label = String

-- | Input index (first input has index 0)
type Input = Int

-- | Node color (e.g. \"#AAA\")
type Color = String

-- | Number of inputs for a node
type Arity = Int

-- | Expression graph
type ExpGraph = [Statement]

-- Create a node
node :: ID -> Label -> Color -> Arity -> ExpGraph
node id lab col ar = return $ NodeStatement
    (NodeId (NameId (show id)) Nothing)
    [ AttributeSetValue (NameId "fillcolor") (NameId col)
    , AttributeSetValue (NameId "label") (NameId labStr)
    ]
  where
    labStr = concat
      [ "<"
      , "<TABLE BORDER=\"0\" CELLBORDER=\"0\" CELLSPACING=\"0\">"
      , "<TR>"
      , "<TD>"
      , lab
      , "</TD>"
      , concatMap mkInp [0 .. ar-1]
      , "</TR>"
      , "</TABLE>"
      , ">"
      ]
    mkInp inp = concat
      [ "<TD PORT=\"inp"
      , show inp
      , "\"> &nbsp;&nbsp;"
      , "</TD>"
      ]

-- Create an edge
edge
    :: ID     -- ^ Downstream node
    -> Input  -- ^ Input index of downstream node
    -> ID     -- ^ Upstream node
    -> ExpGraph
edge from inp to =
    [ NodeStatement
        ( NodeId
            (NameId (show from))
            (Just (PortI (NameId ("inp" ++ show inp ++ ":c")) Nothing))
              -- ":c" is a hack because the `Compass` type doesn't include a
              -- center direction
        )
        []
    , EdgeStatement
        [ENodeId DirectedEdge (NodeId (NameId (show to)) Nothing)]
        []
    ]

-- | Create a sub-graph
subGraph :: ID -> ExpGraph -> ExpGraph
subGraph id
    = return
    . SubgraphStatement
    . NewSubgraph (Just (StringId ("cluster_" ++ show id))) . (dotted :)
  where
    dotted = NodeStatement
      (NodeId (NameId "graph") Nothing)
      [ AttributeSetValue (NameId "style") (NameId "dotted")]

setRoundedNode :: ExpGraph
setRoundedNode = return $ NodeStatement
    (NodeId (NameId "node") Nothing)
    [ AttributeSetValue (NameId "style") (StringId "rounded,filled")
    , AttributeSetValue (NameId "shape") (NameId "box")
    ]

setEdgeStyle :: ExpGraph
setEdgeStyle = return $ NodeStatement
    (NodeId (NameId "edge") Nothing)
    [ AttributeSetValue (NameId "dir") (NameId "both")
    , AttributeSetValue (NameId "arrowtail") (NameId "dot")
    , AttributeSetValue (NameId "tailclip") (NameId "false")
    ]

renderGraph :: ExpGraph -> FilePath -> IO ()
renderGraph g file
    = writeFile file
    $ renderDot
    $ Graph UnstrictGraph DirectedGraph Nothing
    $ concat
        [ setRoundedNode
        , setEdgeStyle
        , g
        ]

