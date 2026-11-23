import LeanCov.CLI

unsafe def main (args : List String) : IO UInt32 :=
  LeanCov.CLI.runCLI args
