{-# LANGUAGE GADTs, DataKinds, TypeOperators, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, KindSignatures, ImpredicativeTypes, PartialTypeSignatures #-}
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

state :: Lens' (Automaton qs as f q) qs; state = lenses (Name :: Name "state")
alphabet :: Lens' (Automaton qs as f q) as; alphabet = lenses (Name :: Name "alphabet")
transition :: Lens' (Automaton qs as f q) f; transition = lenses (Name :: Name "transition")
initial :: Lens' (Automaton qs as f q) q; initial = lenses (Name :: Name "initial")
final :: Lens' (Automaton qs as f q) qs; final = lenses (Name :: Name "final")

type St = String
type NA s = Automaton [s] [Char] [(s, Char, s)] s

convertNA :: (s -> s') -> NA s -> NA s'
convertNA (f :: s -> s') at =
  sinsert (Tag $ fmap f (at^.state) :: "state" :< [s']) $
  sinsert (Tag $ at^.alphabet :: "alphabet" :< String) $
  sinsert (Tag $ fmap (\(a,b,c) -> (f a,b,f c)) (at^.transition) :: "transition" :< [(s',Char,s')]) $
  sinsert (Tag $ f (at^.initial) :: "initial" :< s') $
  sinsert (Tag $ fmap f (at^.final) :: "final" :< [s']) $
  Union HNil

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

deltaMap :: (Eq s) => NA s -> [s] -> Char -> [s]
deltaMap at qs c = nub [q' | (q,c',q') <- (at^.transition), q `elem` qs, c == c']

isDFA :: (Eq s) => NA s -> Bool
isDFA at = all (\(q,c) -> length (deltaMap at [q] c) == 1) $ zip (at ^. state) (at ^. alphabet)

convertNFAtoDFA :: (Eq s, Ord s) => NA s -> NA [s]
convertNFAtoDFA (at :: NA s) =
  sinsert (Tag qs :: "state" :< [[s]]) $
  sinsert (Tag (at^.alphabet) :: "alphabet" :< String) $
  sinsert (Tag d :: "transition" :< [([s], Char, [s])]) $
  sinsert (Tag [at^.initial] :: "initial" :< [s]) $
  sinsert (Tag f :: "final" :< [[s]]) $
  Union HNil
  where
    (qs,d,f) = go [[at^.initial]] [] [] []

    go [] qs d f = (qs,d,f)
    go (q':ws) qs d f = go w' qs' d' f'
      where
        qs' = q' : qs
        f' = if q' `intersect` (at ^. final) /= [] then (q':f) else f
        w' = nub $ [deltaMap at q' c | c <- at^.alphabet, deltaMap at q' c `notElem` qs'] ++ ws
        d' = nub $ [(q',c,deltaMap at q' c) | c <- at^.alphabet] ++ d

buildNA :: (Eq s, Show s) => NA s -> String
buildNA at = _data where
  _data = "{ nodes: " ++ _nodes ++ ", edges: " ++ _edges ++ " }"
  _nodes = (\x -> "[" ++ x ++ "]") $ intercalate "," $ fmap _node (at ^. state)
  _edges = (\x -> "[" ++ x ++ "]") $ intercalate "," $ fmap _edge (at ^. transition)
  _node x = "{data: {label: " ++ show x ++ ", id: " ++ show x ++ ", color: " ++ _color x ++ "}}"
  _edge (q,a,q') = "{data: {source: " ++ show q ++ ", target: " ++ show q' ++ ", label: " ++ show a ++ "}}"
  _final x = let b = x `elem` (at ^. final) in if b then "true" else "false"
  _color x
    | x `elem` (at ^. final) = "'#494'"
    | x == (at ^. initial) = "'#c4f'"
    | otherwise = "'#f94'"

buildTbodyHTML :: [[String]] -> String
buildTbodyHTML ss = _tbody where
  _tbody = concat $ fmap _tr ss
  _tr s = "<tr>" ++ (concat $ fmap _td s) ++ "</tr>"
  _td x = "<td>" ++ x ++ "</td>"

stateNAHTML :: NA St -> String
stateNAHTML at = buildTbodyHTML $ (++ [[_input, _buttonAdd]]) $ fmap (\(i,q) -> [q, _checkbox i q, _buttonDelete i]) $ zip [1..] (at ^. state) where
  _checkbox i q = "<input type=\"checkbox\" id=\"state-final-" ++ show i ++ "\"" ++ checked q ++ ">"
  _buttonDelete i = "<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-state-" ++ show i ++ "\">削除</button>"
  _buttonAdd = "<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-state\">追加</button>"
  _input = "<input type=\"text\" class=\"form-control input-sm\" id=\"new-state\">"

  checked q = if q `elem` (at ^. final) then " checked=\"checked\"" else ""

alphabetNAHTML :: NA St -> String
alphabetNAHTML at = buildTbodyHTML $ (++ [[_text, _buttonAdd]]) $ fmap (\q -> [[q], _buttonDelete [q]]) (at ^. alphabet) where
  _buttonDelete q = "<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-alphabet-" ++ q ++ "\">削除</button>"
  _text = "<input type=\"text\" class=\"form-control input-sm\" id=\"new-alphabet\">"
  _buttonAdd = "<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-alphabet\">追加</button>"

transitionNAHTML :: NA St -> String
transitionNAHTML at = buildTbodyHTML $ (++ [_trLast]) $ fmap (\(i,(q,a,q')) -> [q,[a],q',_buttonDelete i]) $ zip [1..] (at ^. transition) where
  _buttonDelete i = "<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"delete-transition-" ++ show i ++ "\">削除</button>"
  _trLast = [_stateSelect "select-source", _alphabetSelect, _stateSelect "select-target", _buttonAdd]
  _stateSelect k = "<select class=\"form-control input-sm\" id=\"" ++ k ++ "\">" ++ _optionState ++ "</select>"
  _optionState = concat $ fmap (\x -> "<option>" ++ x ++ "</option>") (at ^. state)
  _alphabetSelect = "<select class=\"form-control input-sm\" id=\"select-alphabet\">" ++ _optionAlphabet ++ "</select>"
  _optionAlphabet = concat $ fmap (\x -> "<option>" ++ [x] ++ "</option>") (at ^. alphabet)
  _buttonAdd = "<button type=\"submit\" class=\"btn btn-xs btn-primary\" id=\"add-transition\">追加</button>"

wordListHTML :: [(String, Bool)] -> String
wordListHTML ss = buildTbodyHTML $ fmap (\(s,b) -> [s, resultSpan b]) ss where
  resultSpan True = "<span class=\"label label-success\">O</span>"
  resultSpan False = "<span class=\"label label-danger\">X</span>"

exampleTableHTML :: [(String, String)] -> String
exampleTableHTML ss = buildTbodyHTML $ fmap (\(i,(x,y)) -> [x,y,"<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"load-" ++ show i ++ "\">Load</button>"]) $ zip [1..] ss

conversionTableHTML :: [String] -> String
conversionTableHTML ss = buildTbodyHTML $ fmap (\(i,x) -> [x,"<button type=\"submit\" class=\"btn btn-xs btn-default\" id=\"convert-" ++ show i ++ "\">Go</button>"]) $ zip [1..] ss

drawNA :: (Eq s, Show s) => IORef (NA s) -> IO ()
drawNA ref = do
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
\ elements: " ++ buildNA at ++ ", \
\ layout: { \
\   name: 'cose', \
\   directed: true, \
\   roots: '#a' \
\ } \
\ }); \
\  "
  return ()

runOnNA :: (Eq s) => NA s -> [Char] -> [s]
runOnNA at cs = go [at ^. initial] cs where
  go qs [] = qs
  go qs (c:cs) =
    let qs' = [q' | q' <- at ^. state, q <- qs, (q,c,q') `elem` (at ^. transition)]
    in go qs' cs

accepted :: (Eq s) => NA s -> [Char] -> Bool
accepted at cs = runOnNA at cs `intersect` (at ^. final) /= []

mainloop ref = do
  drawNA ref

  withElem "state-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ stateNAHTML at

  at <- readIORef ref
  forM_ (zip [1..] (at ^. state)) $ \(i,q) -> do
    withElem ("delete-state-" ++ show i) $ \e -> do
      onEvent e Click $ \_ -> do
        modifyIORef ref $ (state %~ delete q)
        mainloop ref

    withElem ("state-final-" ++ show i) $ \e -> do
      onEvent e Click $ \_ -> do
        t <- getProp e "checked"
        case t of
          "true" -> modifyIORef ref $ (final %~ (q :))
          "false" -> modifyIORef ref $ (final %~ delete q)
        mainloop ref

  withElem "add-state" $ \e -> do
    onEvent e Click $ \_ -> do
      Just tbox <- elemById "new-state"
      Just t <- getValue tbox
      modifyIORef ref $ (state %~ (++ [t]))
      mainloop ref

  withElem "alphabet-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ alphabetNAHTML at

  -- alphabetを削除するときにそれを含むtransitionも削除するようにする？
  at <- readIORef ref
  forM_ (at ^. alphabet) $ \c -> do
    withElem ("delete-alphabet-" ++ [c]) $ \e -> do
      onEvent e Click $ \_ -> do
        modifyIORef ref $ (alphabet %~ delete c)
        mainloop ref

  withElem "add-alphabet" $ \e -> do
    onEvent e Click $ \_ -> do
      Just tbox <- elemById "new-alphabet"
      Just [t] <- getValue tbox
      modifyIORef ref $ (alphabet %~ (++ [t]))
      mainloop ref

  withElem "transition-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ transitionNAHTML at

  at <- readIORef ref
  forM_ (zip [1..] (at ^. transition)) $ \(i,p) -> do
    withElem ("delete-transition-" ++ show i) $ \e -> do
      onEvent e Click $ \_ -> do
        modifyIORef ref $ (transition %~ delete p)
        mainloop ref

  withElem "add-transition" $ \e -> do
    onEvent e Click $ \_ -> do
      Just sels <- elemById "select-source"
      Just q <- getValue sels

      Just sels <- elemById "select-alphabet"
      Just [a] <- getValue sels

      Just sels <- elemById "select-target"
      Just q' <- getValue sels
      modifyIORef ref $ (transition %~ (nub . (++ [(q,a,q')])))
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
    let ps = [(w,accepted at w) | n <- [5], w <- replicateM n (at ^. alphabet)]
    setProp e "innerHTML" $ wordListHTML ps

  withElem "example-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ exampleTableHTML $ fmap (\(x,y,_) -> (x,y)) exampleTable

    forM_ (zip [1..] exampleTable) $ \(i,(k,_,json)) -> do
      withElem ("load-" ++ show i) $ \t -> do
        onEvent t Click $ \_ -> do
          let Right auto = fromJSON =<< decodeJSON (toJSString json)
          writeIORef ref auto
          mainloop ref

  withElem "conversion-table-tbody" $ \e -> do
    at <- readIORef ref
    setProp e "innerHTML" $ conversionTableHTML $ fmap (\(x,_) -> x) conversionTable

    forM_ (zip [1..] conversionTable) $ \(i,(k,f)) -> do
      withElem ("convert-" ++ show i) $ \t -> do
        onEvent t Click $ \_ -> do
          modifyIORef ref $ convertNA showStrList . f
          mainloop ref

  return ()

showStrList :: [String] -> String
showStrList xs = "[" ++ intercalate "," xs ++ "]"

exampleTable :: [(String,String,String)]
exampleTable = [
  ("exmple1", "NFA", "{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q1\"],[\"q0\",\"b\",\"q2\"],[\"q1\",\"a\",\"q3\"],[\"q2\",\"a\",\"q2\"],[\"q2\",\"b\",\"q3\"],[\"q3\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"),
  ("exmple2", "NFA", "{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"b\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"),
  ("worst NFAtoDFA efficiency", "NFA", "{\"final\":[\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"a\",\"q0\"],[\"q0\",\"b\",\"q0\"],[\"q0\",\"a\",\"q1\"],[\"q1\",\"a\",\"q2\"],[\"q1\",\"b\",\"q2\"],[\"q2\",\"a\",\"q3\"],[\"q2\",\"b\",\"q3\"]],\"alphabet\":\"ab\",\"state\":[\"q0\",\"q1\",\"q2\",\"q3\"]}"),
  ("multiple of 3", "DFA", "{\"final\":[\"q0\",\"q3\"],\"initial\":\"q0\",\"transition\":[[\"q0\",\"0\",\"q0\"],[\"q0\",\"1\",\"q1\"],[\"q1\",\"1\",\"q0\"],[\"q1\",\"0\",\"q2\"],[\"q2\",\"0\",\"q1\"],[\"q2\",\"1\",\"q2\"]],\"alphabet\":\"01\",\"state\":[\"q0\",\"q1\",\"q2\"]}")
  ]

conversionTable :: [(String,(Eq s, Ord s) => NA s -> NA [s])]
conversionTable = [
  ("NFAtoDFA", convertNFAtoDFA)
  ]

main = do
  let Right auto = fromJSON =<< decodeJSON (toJSString $ (\(_,_,c) -> c) $ exampleTable !! 0)
  ref <- newIORef auto
  mainloop ref
