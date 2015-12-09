{-# LANGUAGE GADTs, DataKinds, TypeOperators, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, KindSignatures #-}
import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.JSON
import Haste.Serialize
import Lens.Family2
import MakeLense
import Data.List
import Data.Monoid (Monoid(..), (<>))
import Data.IORef
import Control.Monad
import GHC.TypeLits

type Automaton qs as f q = UnionT '[
  "state" :< qs,
  "alphabet" :< as,
  "transition" :< f,
  "initial" :< q,
  "final" :< qs
  ]

type St = String
type DA = Automaton [St] [Char] [(St, Char, St)] St
type NA = Automaton [St] [String] [(St, String, [St])] St

instance (Serialize a, Serialize b, Serialize c) => Serialize (a,b,c) where
  toJSON (a,b,c) = Arr [toJSON a, toJSON b, toJSON c]
  parseJSON (Arr [a,b,c]) = liftM3 (,,) (parseJSON a) (parseJSON b) (parseJSON c)

instance (Serialize v, KnownSymbol k) => Serialize ((:<) k v) where
  toJSON (Tag t :: k :< v) = Dict [(toJSString $ symbolVal (Name :: Name k), toJSON t)]
  parseJSON (Dict [(_, t)]) = (\t' -> (Tag t' :: k :< v)) <$> parseJSON t

-- {Dict *: JSON} is a monoid
instance Monoid JSON where
  mempty = Dict []
  mappend (Dict xs) (Dict ys) = Dict (xs `mappend` ys)
  mappend _ _ = error "Monoid JSON: out of domain"

class UnionToJSON (xs :: [*]) where
  unionToJSON :: Union xs -> JSON
  jsonToUnion :: JSON -> Parser (Union xs)

instance UnionToJSON '[] where
  unionToJSON (Union HNil) = Dict []
  jsonToUnion (Dict []) = return $ Union HNil

instance (UnionToJSON xs, Serialize x) => UnionToJSON (x ': xs) where
  unionToJSON (Union (HCons x xs)) = toJSON x <> unionToJSON (Union xs)
  jsonToUnion (Dict (x:xs)) = do
    x' <- parseJSON (Dict [x])
    Union xs' <- jsonToUnion (Dict xs)
    return $ Union $ HCons x' xs'

instance (UnionToJSON xs, All Serialize xs) => Serialize (Union xs) where
  toJSON = unionToJSON
  parseJSON = jsonToUnion

deltaDA :: DA -> [(St,Char,St)]
deltaDA at = go [q0] [q0] [] where
  go ws qs acc = let
      ds' = [(q,a,q') | a <- alphas, q <- ws, q' <- states, (q,a,q') `elem` delta]
      ws' = nub $ [q | q <- fmap (\(_,_,q') -> q') ds', q `notElem` qs]
    in
      if ds' == [] then acc else go ws' (qs ++ ws') (acc ++ ds')

  q0 = at ^. lenses (Name :: Name "initial")
  states = at ^. lenses (Name :: Name "state")
  alphas = at ^. lenses (Name :: Name "alphabet")
  delta = at ^. lenses (Name :: Name "transition")

buildDA :: DA -> String
buildDA at = _data where
  _data = "{ nodes: " ++ _nodes ++ ", edges: " ++ _edges ++ " }"
  _nodes = (\x -> "[" ++ x ++ "]") $ intercalate "," $ fmap _node (at ^. lenses (Name :: Name "state"))
  _edges = (\x -> "[" ++ x ++ "]") $ intercalate "," $ fmap _edge (deltaDA at)
  _node x = "{data: {label: " ++ show x ++ ", id: " ++ show x ++ ", color: " ++ _color x ++ "}}"
  _edge (q,a,q') = "{data: {source: " ++ show q ++ ", target: " ++ show q' ++ ", label: " ++ show a ++ "}}"
  _final x = let b = x `elem` (at ^. lenses (Name :: Name "final")) in
    if b then "true" else "false"
  _color x
    | x `elem` (at ^. lenses (Name :: Name "final")) = "'#494'"
    | x == (at ^. lenses (Name :: Name "initial")) = "'#c4f'"
    | otherwise = "'#f94'"

stateDAHTML :: DA -> String
stateDAHTML at = _tbody where
  _tbody = (++ _trLast) $ concat $ fmap _tr (at ^. lenses (Name :: Name "state"))
  _tr q = "<tr>" ++ _td q ++ _td (_tdCheckbox q) ++ _tdButton q ++ "</tr>"
  _td q = "<td>" ++ q ++ "</td>"
  _tdCheckbox q = "<input type=\"checkbox\" id=\"state-final-" ++ q ++ "\"" ++ checked q ++ ">"
  _tdButton q = "<td><button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-state-" ++ q ++ "\">削除</button></td>"
  _trLast =
    "<tr> \
    \  <td><input type=\"text\" class=\"form-control input-sm\" id=\"new-state\"></td> \
    \  <td><button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-state\">追加</button></td> \
    \ </tr> "

  checked q = if q `elem` (at ^. lenses (Name :: Name "final"))
    then " checked=\"checked\""
    else ""

alphabetDAHTML :: DA -> String
alphabetDAHTML at = _tbody where
  _tbody = (++ _trLast) $ concat $ fmap _tr (at ^. lenses (Name :: Name "alphabet"))
  _tr q = "<tr>" ++ _tdLetter [q] ++ _tdButton [q] ++ "</tr>"
  _tdLetter q = "<td>" ++ q ++ "</td>"
  _tdButton q = "<td><button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-alphabet-" ++ q ++ "\">削除</button></td>"
  _trLast =
    "<tr> \
    \  <td><input type=\"text\" class=\"form-control input-sm\" id=\"new-alphabet\"></td> \
    \  <td><button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-alphabet\">追加</button></td> \
    \ </tr> "

transitionDAHTML :: DA -> String
transitionDAHTML at = _tbody where
  _tbody = (++ _trLast) $ concat $ fmap _tr (at ^. lenses (Name :: Name "transition"))
  _tr (q,a,q') = "<tr>" ++ _td q ++ _td [a] ++ _td q' ++ _tdButton (q,a,q') ++ "</tr>"
  _td x = "<td>" ++ x ++ "</td>"
  _tdButton (q,a,q') = "<td><button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-transition-" ++ q ++ "-" ++ [a] ++ "-" ++ q' ++ "\">削除</button></td>"
  _trLast = "<tr>" ++ _td (_stateSelect "select-source") ++ _td _alphabetSelect ++ _td (_stateSelect "select-target") ++ _td _tdButtonAdd ++ "</tr>"
  _stateSelect k = "<select class=\"form-control input-sm\" id=\"" ++ k ++ "\">" ++ _optionState ++ "</select>"
  _optionState = concat $ fmap (\x -> "<option>" ++ x ++ "</option>") (at ^. lenses (Name :: Name "state"))
  _alphabetSelect = "<select class=\"form-control input-sm\" id=\"select-alphabet\">" ++ _optionAlphabet ++ "</select>"
  _optionAlphabet = concat $ fmap (\x -> "<option>" ++ [x] ++ "</option>") (at ^. lenses (Name :: Name "alphabet"))
  _tdButtonAdd = "<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-transition\">追加</button>"

wordListHTML :: [(String, Bool)] -> String
wordListHTML ss = _tbody where
  _tbody = concat $ fmap _tr ss
  _tr (s,t) = "<tr>" ++ _td s ++ _td (resultSpan t) ++ "</tr>"
  _td x = "<td>" ++ x ++ "</td>"

  resultSpan True = "<span class=\"label label-success\">O</span>"
  resultSpan False = "<span class=\"label label-danger\">X</span>"

tupleTableHTML :: [(String, String)] -> String
tupleTableHTML ss = _tbody where
  _tbody = concat $ fmap _tr ss
  _tr (x,y) = "<tr>" ++ _td x ++ _td y ++ _td (_button x) ++ "</tr>"
  _td x = "<td>" ++ x ++ "</td>"
  _button x = "<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"load-" ++ x ++ "\">Load</button>"

drawDA :: IORef DA -> IO ()
drawDA ref = do
  at <- readIORef ref

  eval $ toJSString $ " \
\ var cy = cytoscape({ \
\ container: document.getElementById('cy'), \
\ style: cytoscape.stylesheet() \
\   .selector('node').css({ \
\     'background-color': 'data(color)', \
\     'text-valign': 'center', \
\     'content': 'data(id)' \
\   }) \
\   .selector('edge').css({ \
\     'target-arrow-shape': 'triangle', \
\     'line-color': '#a9f', \
\     'target-arrow-color': '#a9f', \
\     'text-valign': 'top', \
\     'width': 3, \
\     'content': 'data(label)' \
\   }), \
\ elements: " ++ buildDA at ++ ", \
\ layout: { \
\   name: 'cose', \
\   directed: true, \
\   roots: '#a' \
\ } \
\ }); \
\  "
  return ()

runOnDA :: DA -> [Char] -> [St]
runOnDA at cs = go [at ^. lenses (Name :: Name "initial")] cs where
  go qs [] = qs
  go qs (c:cs) = let qs' = [q' | q' <- at ^. lenses (Name :: Name "state"), q <- qs, (q,c,q') `elem` (at ^. lenses (Name :: Name "transition"))]
    in go qs' cs

accepted :: DA -> [Char] -> Bool
accepted at cs = runOnDA at cs `intersect` (at ^. lenses (Name :: Name "final")) /= []

exNA1 :: DA
exNA1 =
  sinsert (Tag ["q0", "q1", "q2", "q3"] :: "state" :< [St]) $
  sinsert (Tag "ab" :: "alphabet" :< String) $
  sinsert (Tag delta :: "transition" :< [(St, Char, St)]) $
  sinsert (Tag "q0" :: "initial" :< St) $
  sinsert (Tag ["q3"] :: "final" :< [St]) $
  Union HNil

  where
    delta = [
      ("q0",'a',"q1"), ("q0",'b',"q2"),
      ("q1",'a',"q3"),
      ("q2",'a',"q2"), ("q2",'b',"q3"),
      ("q3",'b',"q3")
      ]

mainloop ref = do
  drawDA ref

  withElem "state-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ stateDAHTML at

  at <- readIORef ref
  forM_ (at ^. lenses (Name :: Name "state")) $ \q -> do
    withElem ("delete-state-" ++ q) $ \e -> do
      onEvent e Click $ \_ -> do
        modifyIORef ref $ (lenses (Name :: Name "state") %~ delete q)
        mainloop ref

    withElem ("state-final-" ++ q) $ \e -> do
      onEvent e Click $ \_ -> do
        t <- getProp e "checked"
        case t of
          "true" -> modifyIORef ref $ (lenses (Name :: Name "final") %~ (q :))
          "false" -> modifyIORef ref $ (lenses (Name :: Name "final") %~ delete q)
        mainloop ref

  withElem "add-state" $ \e -> do
    onEvent e Click $ \_ -> do
      Just tbox <- elemById "new-state"
      Just t <- getValue tbox
      modifyIORef ref $ (lenses (Name :: Name "state") %~ (++ [t]))
      mainloop ref

  withElem "alphabet-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ alphabetDAHTML at

  -- alphabetを削除するときにそれを含むtransitionも削除するようにする？
  at <- readIORef ref
  forM_ (at ^. lenses (Name :: Name "alphabet")) $ \c -> do
    withElem ("delete-alphabet-" ++ [c]) $ \e -> do
      onEvent e Click $ \_ -> do
        modifyIORef ref $ (lenses (Name :: Name "alphabet") %~ delete c)
        mainloop ref

  withElem "add-alphabet" $ \e -> do
    onEvent e Click $ \_ -> do
      Just tbox <- elemById "new-alphabet"
      Just [t] <- getValue tbox
      modifyIORef ref $ (lenses (Name :: Name "alphabet") %~ (++ [t]))
      mainloop ref

  withElem "transition-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ transitionDAHTML at

  at <- readIORef ref
  forM_ (at ^. lenses (Name :: Name "transition")) $ \(p@(q,a,q')) -> do
    withElem ("delete-transition-" ++ q ++ "-" ++ [a] ++ "-" ++ q') $ \e -> do
      onEvent e Click $ \_ -> do
        modifyIORef ref $ (lenses (Name :: Name "transition") %~ delete p)
        mainloop ref

  withElem "add-transition" $ \e -> do
    onEvent e Click $ \_ -> do
      Just sels <- elemById "select-source"
      Just q <- getValue sels

      Just sels <- elemById "select-alphabet"
      Just [a] <- getValue sels

      Just sels <- elemById "select-target"
      Just q' <- getValue sels
      modifyIORef ref $ (lenses (Name :: Name "transition") %~ (nub . (++ [(q,a,q')])))
      mainloop ref

  withElem "export-button" $ \e -> do
    onEvent e Click $ \_ -> do
      at <- readIORef ref

      Just t <- elemById "export-text"
      setProp t "innerText" $ fromJSStr $ encodeJSON $ toJSON at

  withElem "import-button" $ \e -> do
    onEvent e Click $ \_ -> do
      Just t <- elemById "import-text"
      Just (json :: String) <- getValue t
      let Right auto = fromJSON =<< decodeJSON (toJSString json)
      writeIORef ref auto
      mainloop ref

  withElem "accept-check-button" $ \e -> do
    onEvent e Click $ \_ -> do
      Just t <- elemById "accept-check-text"
      Just (word :: String) <- getValue t

      at <- readIORef ref
      let result = accepted at word
      withElem "accept-check-result" $ \r -> do
        setProp r "innerHTML" $ case result of
          True -> "<span class=\"label label-success\">O</span>"
          False -> "<span class=\"label label-danger\">X</span>"

  withElem "word-table-tbody" $ \e -> do
    at <- readIORef ref
    let ps = [(w,accepted at w) | n <- [5], w <- replicateM n (at ^. lenses (Name :: Name "alphabet"))]
    setProp e "innerHTML" $ wordListHTML ps

  withElem "example-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ tupleTableHTML $ fmap (\(x,y,_) -> (x,y)) exampleTable

    forM_ exampleTable $ \(k,_,json) -> do
      withElem ("load-" ++ k) $ \t -> do
        onEvent t Click $ \_ -> do
          let Right auto = fromJSON =<< decodeJSON (toJSString json)
          writeIORef ref auto
          mainloop ref

  return ()

exampleTable :: [(String,String,String)]
exampleTable = [
  ("exmple1", "NFA", "{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q1\"],[\"q0\",\"b\",\"q2\"],[\"q1\",\"a\",\"q3\"],[\"q2\",\"a\",\"q2\"],[\"q2\",\"b\",\"q3\"],[\"q3\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"),
  ("multiple-of-3", "DFA", "{\"final\":[\"q0\",\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"0\",\"q0\"],[\"q0\",\"1\",\"q1\"],[\"q1\",\"1\",\"q0\"],[\"q1\",\"0\",\"q2\"],[\"q2\",\"0\",\"q1\"],[\"q2\",\"1\",\"q2\"]],\"alphabet\":\"01\",\"state\":[\"q0\",\"q1\",\"q2\"]}")
  ]

main = do
  ref <- newIORef exNA1
  mainloop ref
