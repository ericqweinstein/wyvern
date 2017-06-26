||| Main module.
|||
||| See: https://github.com/idris-lang/Idris-dev/blob/ef3c9d7ca0ce38d2921865b3e5ecd642504e7eaf/samples/ST/Net/Network.idr
module Wyvern.Main

import Control.ST
import Control.ST.ImplicitCall
import Network.Socket

data SocketState = Ready | Bound | Listening | Open | Closed
data CloseOK : SocketState -> Type where
  CloseOpen : CloseOK Open
  CloseListening : CloseOK Listening

interface Sockets (m : Type -> Type) where
  Sock : SocketState -> Type

  socket : SocketType -> ST m (Either () Var) [addIfRight (Sock Ready)]

  bind : (sock : Var) -> (addr : Maybe SocketAddress) -> (port : Port) ->
         ST m (Either () ()) [sock ::: Sock Ready :-> (Sock Closed `or` Sock Bound)]

  listen : (sock : Var) ->
           ST m (Either () ()) [sock ::: Sock Bound :-> (Sock Closed `or` Sock Listening)]

  accept : (sock : Var) ->
           ST m (Either () Var) [sock ::: Sock Listening, addIfRight (Sock Open)]

  connect : (sock : Var) -> SocketAddress -> Port ->
            ST m (Either () ()) [sock ::: Sock Ready :-> (Sock Closed `or` Sock Open)]

  close : (sock : Var) -> {auto prf : CloseOK st} ->
          ST m () [sock ::: Sock st :-> Sock Closed]

  remove : (sock : Var) -> ST m () [Remove sock (Sock Closed)]

  send : (sock : Var) -> String ->
         ST m (Either () ()) [sock ::: Sock Open :-> (Sock Closed `or` Sock Open)]

  recv : (sock : Var) ->
         ST m (Either () String) [sock ::: Sock Open :-> (Sock Closed `or` Sock Open)]

implementation Sockets IO where
  Sock _ = State Socket

  socket ty = do Right sock <- lift $ Socket.socket AF_INET ty 0
                 | Left err => pure (Left ())
                 lbl <- new sock
                 pure (Right lbl)

  bind sock addr port = do ok <- lift $ bind !(read sock) addr port
                           if ok /= 0
                              then pure (Left ())
                              else pure (Right ())

  listen sock = do ok <- lift $ listen !(read sock)
                   if ok /= 0
                      then pure (Left ())
                      else pure (Right ())

  accept sock = do Right (conn, addr) <- lift $ accept !(read sock)
                   | Left err => pure (Left ())
                   lbl <- new conn
                   returning (Right lbl) (toEnd lbl)

  connect sock addr port = do ok <- lift $ connect !(read sock) addr port
                              if ok /= 0
                                 then pure (Left ())
                                 else pure (Right ())

  close sock = do lift $ close !(read sock)
                  pure ()

  remove sock = delete sock

  send sock msg = do Right _ <- lift $ send !(read sock) msg
                     | Left _ => pure (Left ())
                     pure (Right ())

  recv sock = do Right (msg, len) <- lift $ recv !(read sock) 1024
                 | Left _ => pure (Left ())
                 pure (Right msg)

echoServer : (ConsoleIO m, Sockets m) => (sock : Var) ->
             ST m () [remove sock (Sock {m} Listening)]
echoServer sock =
  do Right new <- accept sock                    | Left err => do close sock; remove sock
     Right msg <- recv new                       | Left err => do close sock; remove sock; remove new
     Right ok  <- send new ("You said: " ++ msg) | Left err => do remove new; close sock; remove sock
     close new; remove new; echoServer sock

startServer : (ConsoleIO m, Sockets m) => ST m () []
startServer =
  do Right sock <- socket Stream          | Left err => pure ()
     Right ok   <- bind sock Nothing 4242 | Left err => remove sock
     Right ok   <- listen sock            | Left err => remove sock
     echoServer sock

main : IO ()
main = run startServer
