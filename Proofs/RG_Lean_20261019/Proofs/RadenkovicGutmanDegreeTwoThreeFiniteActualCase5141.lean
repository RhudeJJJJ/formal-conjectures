/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5141 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap5141 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5141 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5141_checked : acceptsGraphIso
    (source (graph core5141) (root 8) 2 4) DegreeTwoThreeSpectrum7034.graph sourceMap5141=true := by decide +kernel
theorem fusedMap5141_checked : acceptsGraphIso
    (fused (graph core5141) (root 8) 2 4) DegreeTwoThreeSpectrum5088.graph fusedMap5141=true := by decide +kernel
theorem certified5141 : Certified (graph core5141) (root 8) 2 4 :=
  of_native_maps core5141 DegreeTwoThreeSpectrum7034.graph DegreeTwoThreeSpectrum5088.graph
    sourceMap5141 fusedMap5141 sourceMap5141_checked fusedMap5141_checked
    DegreeTwoThreeFiniteComparisons.comparison5141
#print axioms sourceMap5141_checked
#print axioms fusedMap5141_checked
#print axioms certified5141
def sourceMap5141swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5141swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5141swap_checked : acceptsGraphIso
    (source (graph core5141) (root 8) 4 2) DegreeTwoThreeSpectrum7034.graph sourceMap5141swap=true := by decide +kernel
theorem fusedMap5141swap_checked : acceptsGraphIso
    (fused (graph core5141) (root 8) 4 2) DegreeTwoThreeSpectrum5088.graph fusedMap5141swap=true := by decide +kernel
theorem certified5141swap : Certified (graph core5141) (root 8) 4 2 :=
  of_native_maps core5141 DegreeTwoThreeSpectrum7034.graph DegreeTwoThreeSpectrum5088.graph
    sourceMap5141swap fusedMap5141swap sourceMap5141swap_checked fusedMap5141swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5141
#print axioms sourceMap5141swap_checked
#print axioms fusedMap5141swap_checked
#print axioms certified5141swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
