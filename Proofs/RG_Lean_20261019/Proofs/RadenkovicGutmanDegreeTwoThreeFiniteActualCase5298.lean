/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5298 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap5298 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,8,9,10,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5298 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5298_checked : acceptsGraphIso
    (source (graph core5298) (root 6) 2 6) DegreeTwoThreeSpectrum6531.graph sourceMap5298=true := by decide +kernel
theorem fusedMap5298_checked : acceptsGraphIso
    (fused (graph core5298) (root 6) 2 6) DegreeTwoThreeSpectrum5009.graph fusedMap5298=true := by decide +kernel
theorem certified5298 : Certified (graph core5298) (root 6) 2 6 :=
  of_native_maps core5298 DegreeTwoThreeSpectrum6531.graph DegreeTwoThreeSpectrum5009.graph
    sourceMap5298 fusedMap5298 sourceMap5298_checked fusedMap5298_checked
    DegreeTwoThreeFiniteComparisons.comparison5298
#print axioms sourceMap5298_checked
#print axioms fusedMap5298_checked
#print axioms certified5298
def sourceMap5298swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,1,0,12,13,14,15,16,8,9,10] (sourceLabel 6 6 2 v)
def fusedMap5298swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5298swap_checked : acceptsGraphIso
    (source (graph core5298) (root 6) 6 2) DegreeTwoThreeSpectrum6531.graph sourceMap5298swap=true := by decide +kernel
theorem fusedMap5298swap_checked : acceptsGraphIso
    (fused (graph core5298) (root 6) 6 2) DegreeTwoThreeSpectrum5009.graph fusedMap5298swap=true := by decide +kernel
theorem certified5298swap : Certified (graph core5298) (root 6) 6 2 :=
  of_native_maps core5298 DegreeTwoThreeSpectrum6531.graph DegreeTwoThreeSpectrum5009.graph
    sourceMap5298swap fusedMap5298swap sourceMap5298swap_checked fusedMap5298swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5298
#print axioms sourceMap5298swap_checked
#print axioms fusedMap5298swap_checked
#print axioms certified5298swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
