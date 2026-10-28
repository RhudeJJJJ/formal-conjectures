/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5060 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5060 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,8,5,6,7,9,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap5060 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap5060_checked : acceptsGraphIso
    (source (graph core5060) (root 5) 2 4) DegreeTwoThreeSpectrum1905.graph sourceMap5060=true := by decide +kernel
theorem fusedMap5060_checked : acceptsGraphIso
    (fused (graph core5060) (root 5) 2 4) DegreeTwoThreeSpectrum1734.graph fusedMap5060=true := by decide +kernel
theorem certified5060 : Certified (graph core5060) (root 5) 2 4 :=
  of_native_maps core5060 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap5060 fusedMap5060 sourceMap5060_checked fusedMap5060_checked
    DegreeTwoThreeFiniteComparisons.comparison5060
#print axioms sourceMap5060_checked
#print axioms fusedMap5060_checked
#print axioms certified5060
def sourceMap5060swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,5,6,7] (sourceLabel 5 4 2 v)
def fusedMap5060swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap5060swap_checked : acceptsGraphIso
    (source (graph core5060) (root 5) 4 2) DegreeTwoThreeSpectrum1905.graph sourceMap5060swap=true := by decide +kernel
theorem fusedMap5060swap_checked : acceptsGraphIso
    (fused (graph core5060) (root 5) 4 2) DegreeTwoThreeSpectrum1734.graph fusedMap5060swap=true := by decide +kernel
theorem certified5060swap : Certified (graph core5060) (root 5) 4 2 :=
  of_native_maps core5060 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap5060swap fusedMap5060swap sourceMap5060swap_checked fusedMap5060swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5060
#print axioms sourceMap5060swap_checked
#print axioms fusedMap5060swap_checked
#print axioms certified5060swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
