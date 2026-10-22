/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5231 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap5231 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5231 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5231_checked : acceptsGraphIso
    (source (graph core5231) (root 6) 2 5) DegreeTwoThreeSpectrum4235.graph sourceMap5231=true := by decide +kernel
theorem fusedMap5231_checked : acceptsGraphIso
    (fused (graph core5231) (root 6) 2 5) DegreeTwoThreeSpectrum3907.graph fusedMap5231=true := by decide +kernel
theorem certified5231 : Certified (graph core5231) (root 6) 2 5 :=
  of_native_maps core5231 DegreeTwoThreeSpectrum4235.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap5231 fusedMap5231 sourceMap5231_checked fusedMap5231_checked
    DegreeTwoThreeFiniteComparisons.comparison5231
#print axioms sourceMap5231_checked
#print axioms fusedMap5231_checked
#print axioms certified5231
def sourceMap5231swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,7,8,9] (sourceLabel 6 5 2 v)
def fusedMap5231swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5231swap_checked : acceptsGraphIso
    (source (graph core5231) (root 6) 5 2) DegreeTwoThreeSpectrum4235.graph sourceMap5231swap=true := by decide +kernel
theorem fusedMap5231swap_checked : acceptsGraphIso
    (fused (graph core5231) (root 6) 5 2) DegreeTwoThreeSpectrum3907.graph fusedMap5231swap=true := by decide +kernel
theorem certified5231swap : Certified (graph core5231) (root 6) 5 2 :=
  of_native_maps core5231 DegreeTwoThreeSpectrum4235.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap5231swap fusedMap5231swap sourceMap5231swap_checked fusedMap5231swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5231
#print axioms sourceMap5231swap_checked
#print axioms fusedMap5231swap_checked
#print axioms certified5231swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
