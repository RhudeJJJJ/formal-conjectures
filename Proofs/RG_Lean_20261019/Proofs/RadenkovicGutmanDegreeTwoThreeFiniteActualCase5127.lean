/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5127 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap5127 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5127 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5127_checked : acceptsGraphIso
    (source (graph core5127) (root 8) 2 4) DegreeTwoThreeSpectrum6333.graph sourceMap5127=true := by decide +kernel
theorem fusedMap5127_checked : acceptsGraphIso
    (fused (graph core5127) (root 8) 2 4) DegreeTwoThreeSpectrum4977.graph fusedMap5127=true := by decide +kernel
theorem certified5127 : Certified (graph core5127) (root 8) 2 4 :=
  of_native_maps core5127 DegreeTwoThreeSpectrum6333.graph DegreeTwoThreeSpectrum4977.graph
    sourceMap5127 fusedMap5127 sourceMap5127_checked fusedMap5127_checked
    DegreeTwoThreeFiniteComparisons.comparison5127
#print axioms sourceMap5127_checked
#print axioms fusedMap5127_checked
#print axioms certified5127
def sourceMap5127swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5127swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5127swap_checked : acceptsGraphIso
    (source (graph core5127) (root 8) 4 2) DegreeTwoThreeSpectrum6333.graph sourceMap5127swap=true := by decide +kernel
theorem fusedMap5127swap_checked : acceptsGraphIso
    (fused (graph core5127) (root 8) 4 2) DegreeTwoThreeSpectrum4977.graph fusedMap5127swap=true := by decide +kernel
theorem certified5127swap : Certified (graph core5127) (root 8) 4 2 :=
  of_native_maps core5127 DegreeTwoThreeSpectrum6333.graph DegreeTwoThreeSpectrum4977.graph
    sourceMap5127swap fusedMap5127swap sourceMap5127swap_checked fusedMap5127swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5127
#print axioms sourceMap5127swap_checked
#print axioms fusedMap5127swap_checked
#print axioms certified5127swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
