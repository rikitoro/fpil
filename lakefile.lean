import Lake
open Lake DSL

package «fpil» {
  -- add package configuration options here
}

lean_lib «Fpil» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fpil» {
  root := `Main
}
