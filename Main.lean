import AVLSet.Tree
import AVLSet.Set
import AVLSet.Tests
import AVLSet.PropertyTests

def main : IO Unit := do
  -- Unit тесты
  AVLSetTests.runAllTests
  
  -- Property-based тесты
  AVLSetPropertyTests.runPropertyTests
