/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2083 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap2083 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11] (sourceLabel 7 0 4 v)
def fusedMap2083 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2083_checked : acceptsGraphIso
    (source (graph core2083) (root 7) 0 4) DegreeTwoThreeSpectrum1803.graph sourceMap2083=true := by decide +kernel
theorem fusedMap2083_checked : acceptsGraphIso
    (fused (graph core2083) (root 7) 0 4) DegreeTwoThreeSpectrum1713.graph fusedMap2083=true := by decide +kernel
theorem certified2083 : Certified (graph core2083) (root 7) 0 4 :=
  of_native_maps core2083 DegreeTwoThreeSpectrum1803.graph DegreeTwoThreeSpectrum1713.graph
    sourceMap2083 fusedMap2083 sourceMap2083_checked fusedMap2083_checked
    DegreeTwoThreeFiniteComparisons.comparison2083
#print axioms sourceMap2083_checked
#print axioms fusedMap2083_checked
#print axioms certified2083
def sourceMap2083swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,12,7,8,9,10,11,13] (sourceLabel 7 4 0 v)
def fusedMap2083swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2083swap_checked : acceptsGraphIso
    (source (graph core2083) (root 7) 4 0) DegreeTwoThreeSpectrum1803.graph sourceMap2083swap=true := by decide +kernel
theorem fusedMap2083swap_checked : acceptsGraphIso
    (fused (graph core2083) (root 7) 4 0) DegreeTwoThreeSpectrum1713.graph fusedMap2083swap=true := by decide +kernel
theorem certified2083swap : Certified (graph core2083) (root 7) 4 0 :=
  of_native_maps core2083 DegreeTwoThreeSpectrum1803.graph DegreeTwoThreeSpectrum1713.graph
    sourceMap2083swap fusedMap2083swap sourceMap2083swap_checked fusedMap2083swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2083
#print axioms sourceMap2083swap_checked
#print axioms fusedMap2083swap_checked
#print axioms certified2083swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
