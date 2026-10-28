/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5404 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5404 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5,11,12,13,14,15,16] (sourceLabel 5 4 5 v)
def fusedMap5404 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 4 5 v)
theorem sourceMap5404_checked : acceptsGraphIso
    (source (graph core5404) (root 5) 4 5) DegreeTwoThreeSpectrum5917.graph sourceMap5404=true := by decide +kernel
theorem fusedMap5404_checked : acceptsGraphIso
    (fused (graph core5404) (root 5) 4 5) DegreeTwoThreeSpectrum4987.graph fusedMap5404=true := by decide +kernel
theorem certified5404 : Certified (graph core5404) (root 5) 4 5 :=
  of_native_maps core5404 DegreeTwoThreeSpectrum5917.graph DegreeTwoThreeSpectrum4987.graph
    sourceMap5404 fusedMap5404 sourceMap5404_checked fusedMap5404_checked
    DegreeTwoThreeFiniteComparisons.comparison5404
#print axioms sourceMap5404_checked
#print axioms fusedMap5404_checked
#print axioms certified5404
def sourceMap5404swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5] (sourceLabel 5 5 4 v)
def fusedMap5404swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 5 4 v)
theorem sourceMap5404swap_checked : acceptsGraphIso
    (source (graph core5404) (root 5) 5 4) DegreeTwoThreeSpectrum5917.graph sourceMap5404swap=true := by decide +kernel
theorem fusedMap5404swap_checked : acceptsGraphIso
    (fused (graph core5404) (root 5) 5 4) DegreeTwoThreeSpectrum4987.graph fusedMap5404swap=true := by decide +kernel
theorem certified5404swap : Certified (graph core5404) (root 5) 5 4 :=
  of_native_maps core5404 DegreeTwoThreeSpectrum5917.graph DegreeTwoThreeSpectrum4987.graph
    sourceMap5404swap fusedMap5404swap sourceMap5404swap_checked fusedMap5404swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5404
#print axioms sourceMap5404swap_checked
#print axioms fusedMap5404swap_checked
#print axioms certified5404swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
