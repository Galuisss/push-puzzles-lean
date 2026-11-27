import Lake

open Lake DSL

package push_puzzle where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require «cslib-frontier» from git
  "https://github.com/cslib-community/cslib-frontier" @
  "3a8c6423f4144d625e122c6d24ba94a36fcacc95"

lean_lib PushFS
lean_lib PushS
lean_lib Push
lean_lib PushPush
lean_lib PushPushS
lean_lib PushPushFS
lean_lib PushPushF

@[default_target]
lean_lib PushPuzzle
