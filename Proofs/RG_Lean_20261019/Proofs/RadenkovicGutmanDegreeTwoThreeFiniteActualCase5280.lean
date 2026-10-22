/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5280 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5280 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,6,7,8,3,4,5,1,0,9,10,11,12,13] (sourceLabel 3 2 6 v)
def fusedMap5280 : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 2 6 v)
theorem sourceMap5280_checked : acceptsGraphIso
    (source (graph core5280) (root 3) 2 6) DegreeTwoThreeSpectrum1870.graph sourceMap5280=true := by decide +kernel
theorem fusedMap5280_checked : acceptsGraphIso
    (fused (graph core5280) (root 3) 2 6) DegreeTwoThreeSpectrum1722.graph fusedMap5280=true := by decide +kernel
theorem certified5280 : Certified (graph core5280) (root 3) 2 6 :=
  of_native_maps core5280 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap5280 fusedMap5280 sourceMap5280_checked fusedMap5280_checked
    DegreeTwoThreeFiniteComparisons.comparison5280
#print axioms sourceMap5280_checked
#print axioms fusedMap5280_checked
#print axioms certified5280
def sourceMap5280swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,6,7,8,1,0,9,10,11,12,13,3,4,5] (sourceLabel 3 6 2 v)
def fusedMap5280swap : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 6 2 v)
theorem sourceMap5280swap_checked : acceptsGraphIso
    (source (graph core5280) (root 3) 6 2) DegreeTwoThreeSpectrum1870.graph sourceMap5280swap=true := by decide +kernel
theorem fusedMap5280swap_checked : acceptsGraphIso
    (fused (graph core5280) (root 3) 6 2) DegreeTwoThreeSpectrum1722.graph fusedMap5280swap=true := by decide +kernel
theorem certified5280swap : Certified (graph core5280) (root 3) 6 2 :=
  of_native_maps core5280 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap5280swap fusedMap5280swap sourceMap5280swap_checked fusedMap5280swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5280
#print axioms sourceMap5280swap_checked
#print axioms fusedMap5280swap_checked
#print axioms certified5280swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
