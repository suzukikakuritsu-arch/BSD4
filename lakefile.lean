import Lake
open Lake DSL

package bsd {
  -- プロジェクト設定
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib BSD {
  -- ライブラリ設定
}
