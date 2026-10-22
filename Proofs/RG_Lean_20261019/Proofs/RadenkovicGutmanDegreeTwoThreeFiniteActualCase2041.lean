/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2041 : Family 10 := level10.get ⟨1741,by decide⟩
def sourceMap2041 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap2041 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2041_checked : acceptsGraphIso
    (source (graph core2041) (root 10) 0 2) DegreeTwoThreeSpectrum3838.graph sourceMap2041=true := by decide +kernel
theorem fusedMap2041_checked : acceptsGraphIso
    (fused (graph core2041) (root 10) 0 2) DegreeTwoThreeSpectrum3464.graph fusedMap2041=true := by decide +kernel
theorem certified2041 : Certified (graph core2041) (root 10) 0 2 :=
  of_native_maps core2041 DegreeTwoThreeSpectrum3838.graph DegreeTwoThreeSpectrum3464.graph
    sourceMap2041 fusedMap2041 sourceMap2041_checked fusedMap2041_checked
    DegreeTwoThreeFiniteComparisons.comparison2041
#print axioms sourceMap2041_checked
#print axioms fusedMap2041_checked
#print axioms certified2041
def sourceMap2041swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap2041swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2041swap_checked : acceptsGraphIso
    (source (graph core2041) (root 10) 2 0) DegreeTwoThreeSpectrum3838.graph sourceMap2041swap=true := by decide +kernel
theorem fusedMap2041swap_checked : acceptsGraphIso
    (fused (graph core2041) (root 10) 2 0) DegreeTwoThreeSpectrum3464.graph fusedMap2041swap=true := by decide +kernel
theorem certified2041swap : Certified (graph core2041) (root 10) 2 0 :=
  of_native_maps core2041 DegreeTwoThreeSpectrum3838.graph DegreeTwoThreeSpectrum3464.graph
    sourceMap2041swap fusedMap2041swap sourceMap2041swap_checked fusedMap2041swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2041
#print axioms sourceMap2041swap_checked
#print axioms fusedMap2041swap_checked
#print axioms certified2041swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
