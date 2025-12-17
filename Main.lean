-- Main.lean
import AVLSet.Tree
import AVLSet.Set
import AVLSet.Tests
import AVLSet.PropertyTests
import AVLSet.Proofs

def main : IO Unit := do
  -- Модульные тесты
  AVLSetTests.runAllTests
  
  -- Property-based тесты
  AVLSetPropertyTests.runPropertyTests
  
  -- Демонстрация формальных доказательств
  AVLSetProofs.runProofDemonstrations
