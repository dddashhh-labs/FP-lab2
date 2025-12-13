import Lake
open Lake DSL

package «avlset» {
  -- add package configuration options here
}

lean_lib «AVLSet» {
  roots := #[`AVLSet]
}

@[default_target]
lean_exe «avlset» {
  root := `Main
}
