/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2031 : Family 10 := level10.get ⟨1713,by decide⟩
def sourceMap2031 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2031 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2031_checked : acceptsGraphIso
    (source (graph core2031) (root 10) 0 2) DegreeTwoThreeSpectrum3825.graph sourceMap2031=true := by decide +kernel
theorem fusedMap2031_checked : acceptsGraphIso
    (fused (graph core2031) (root 10) 0 2) DegreeTwoThreeSpectrum3393.graph fusedMap2031=true := by decide +kernel
theorem certified2031 : Certified (graph core2031) (root 10) 0 2 :=
  of_native_maps core2031 DegreeTwoThreeSpectrum3825.graph DegreeTwoThreeSpectrum3393.graph
    sourceMap2031 fusedMap2031 sourceMap2031_checked fusedMap2031_checked
    DegreeTwoThreeFiniteComparisons.comparison2031
#print axioms sourceMap2031_checked
#print axioms fusedMap2031_checked
#print axioms certified2031
def sourceMap2031swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2031swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2031swap_checked : acceptsGraphIso
    (source (graph core2031) (root 10) 2 0) DegreeTwoThreeSpectrum3825.graph sourceMap2031swap=true := by decide +kernel
theorem fusedMap2031swap_checked : acceptsGraphIso
    (fused (graph core2031) (root 10) 2 0) DegreeTwoThreeSpectrum3393.graph fusedMap2031swap=true := by decide +kernel
theorem certified2031swap : Certified (graph core2031) (root 10) 2 0 :=
  of_native_maps core2031 DegreeTwoThreeSpectrum3825.graph DegreeTwoThreeSpectrum3393.graph
    sourceMap2031swap fusedMap2031swap sourceMap2031swap_checked fusedMap2031swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2031
#print axioms sourceMap2031swap_checked
#print axioms fusedMap2031swap_checked
#print axioms certified2031swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
