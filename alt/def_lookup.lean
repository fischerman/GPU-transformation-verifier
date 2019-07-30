import system.io

namespace def_lookup

open tactic

def a := "hello world"
++ "hi"
++ "hi"
++ "hi"
++ "hi"
++ "hi"

def name.from_dotted_string (s : string) : name := (s.split (λc, c = '.')).foldl (λ n s, name.mk_string s n) name.anonymous

meta def find_def (n : name) : tactic (string × pos) := do
  env ← get_env,
  pos ← environment.decl_pos env n,
  file ← environment.decl_olean env n,
  return (file, pos)

-- run_cmd find_def (name.from_dotted_string "nat.add") >>= trace

-- run_cmd trace $ ("nat.add".split (λc, c = '.')).foldl (λ n s, name.mk_string s n) name.anonymous

meta def print_def (fd outfd : io.handle) : io unit := do
    line ← io.fs.get_line fd,
    stdout ← io.stdout, -- stdout doesn't render UTF-8 properly
    if line.to_string ≠ "\n" then (do io.fs.write outfd line, print_def) else return ()

meta def main : io unit := do
  args ← io.cmdline_args,
  match args with
  | (n :: out :: []) := do
    (file, pos) ← io.run_tactic $ find_def (name.from_dotted_string n),
    stderr ← io.stderr,
    io.fs.put_str_ln stderr file,
    fd ← io.mk_file_handle file io.mode.read tt,
    -- skip over lines
    (list.range $ pos.line - 1).mmap' (λi, io.fs.get_line fd),
    -- print to the next empty line
    outfd ← io.mk_file_handle out io.mode.write tt <|> io.mk_file_handle out io.mode.append tt,
    print_def fd outfd
  | _ := io.fail "syntax: lean --run file.lean [name]"
  end

end def_lookup