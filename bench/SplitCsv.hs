#!/usr/bin/env runhaskell
import System.Directory
import System.FilePath

processFile f = do
  c <- readFile f
  let header : contents = lines c
      file = takeBaseName f
      run [] = return ()
      run (l:ls) = 
        case span (/= '/') l of
          (gname, _:rest) -> do
            let fname = "processed" </> file ++ "_" ++ gname ++ ".csv"
            writeFile fname (unlines [header,rest])
            runGroup gname fname ls
          _  -> error "run: unexpected line"
      runGroup _ _ [] = return ()
      runGroup gname fname (l:ls) = 
        case span (/= '/') l of
         (gname', _:rest)
           | gname' == gname -> appendFile fname (rest ++ "\n") >> runGroup gname fname ls
           | otherwise -> run (l:ls)
         _ -> error "runGroup: unexpected line"
  run contents
  return ()

main = do
  createDirectoryIfMissing False "processed"
  fs <- getDirectoryContents "."
  let csvs = filter (\ f -> takeExtension f == ".csv") fs
  mapM_ processFile csvs
