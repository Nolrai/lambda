import Lake
open Lake DSL

package lambda {
  -- add package configuration options here
}

lean_lib Lambda {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe lambda {
  root := `Main
}
