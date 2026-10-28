/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5078 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap5078 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,8,9,10,5,6,7,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5078 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5078_checked : acceptsGraphIso
    (source (graph core5078) (root 6) 2 4) DegreeTwoThreeSpectrum3614.graph sourceMap5078=true := by decide +kernel
theorem fusedMap5078_checked : acceptsGraphIso
    (fused (graph core5078) (root 6) 2 4) DegreeTwoThreeSpectrum2382.graph fusedMap5078=true := by decide +kernel
theorem certified5078 : Certified (graph core5078) (root 6) 2 4 :=
  of_native_maps core5078 DegreeTwoThreeSpectrum3614.graph DegreeTwoThreeSpectrum2382.graph
    sourceMap5078 fusedMap5078 sourceMap5078_checked fusedMap5078_checked
    DegreeTwoThreeFiniteComparisons.comparison5078
#print axioms sourceMap5078_checked
#print axioms fusedMap5078_checked
#print axioms certified5078
def sourceMap5078swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,8,9,10,0,11,12,13,14,5,6,7] (sourceLabel 6 4 2 v)
def fusedMap5078swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5078swap_checked : acceptsGraphIso
    (source (graph core5078) (root 6) 4 2) DegreeTwoThreeSpectrum3614.graph sourceMap5078swap=true := by decide +kernel
theorem fusedMap5078swap_checked : acceptsGraphIso
    (fused (graph core5078) (root 6) 4 2) DegreeTwoThreeSpectrum2382.graph fusedMap5078swap=true := by decide +kernel
theorem certified5078swap : Certified (graph core5078) (root 6) 4 2 :=
  of_native_maps core5078 DegreeTwoThreeSpectrum3614.graph DegreeTwoThreeSpectrum2382.graph
    sourceMap5078swap fusedMap5078swap sourceMap5078swap_checked fusedMap5078swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5078
#print axioms sourceMap5078swap_checked
#print axioms fusedMap5078swap_checked
#print axioms certified5078swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
