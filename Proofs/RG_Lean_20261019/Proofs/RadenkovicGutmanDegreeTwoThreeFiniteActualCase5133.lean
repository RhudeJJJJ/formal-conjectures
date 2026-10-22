/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5133 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap5133 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5133 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5133_checked : acceptsGraphIso
    (source (graph core5133) (root 8) 2 4) DegreeTwoThreeSpectrum6745.graph sourceMap5133=true := by decide +kernel
theorem fusedMap5133_checked : acceptsGraphIso
    (fused (graph core5133) (root 8) 2 4) DegreeTwoThreeSpectrum5024.graph fusedMap5133=true := by decide +kernel
theorem certified5133 : Certified (graph core5133) (root 8) 2 4 :=
  of_native_maps core5133 DegreeTwoThreeSpectrum6745.graph DegreeTwoThreeSpectrum5024.graph
    sourceMap5133 fusedMap5133 sourceMap5133_checked fusedMap5133_checked
    DegreeTwoThreeFiniteComparisons.comparison5133
#print axioms sourceMap5133_checked
#print axioms fusedMap5133_checked
#print axioms certified5133
def sourceMap5133swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5133swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5133swap_checked : acceptsGraphIso
    (source (graph core5133) (root 8) 4 2) DegreeTwoThreeSpectrum6745.graph sourceMap5133swap=true := by decide +kernel
theorem fusedMap5133swap_checked : acceptsGraphIso
    (fused (graph core5133) (root 8) 4 2) DegreeTwoThreeSpectrum5024.graph fusedMap5133swap=true := by decide +kernel
theorem certified5133swap : Certified (graph core5133) (root 8) 4 2 :=
  of_native_maps core5133 DegreeTwoThreeSpectrum6745.graph DegreeTwoThreeSpectrum5024.graph
    sourceMap5133swap fusedMap5133swap sourceMap5133swap_checked fusedMap5133swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5133
#print axioms sourceMap5133swap_checked
#print axioms fusedMap5133swap_checked
#print axioms certified5133swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
