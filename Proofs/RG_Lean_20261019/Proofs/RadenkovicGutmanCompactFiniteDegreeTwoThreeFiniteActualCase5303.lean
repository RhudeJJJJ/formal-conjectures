/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5303 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap5303 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,11,3,4,5,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5303 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5303_checked : acceptsGraphIso
    (source (graph core5303) (root 6) 2 6) DegreeTwoThreeSpectrum6869.graph sourceMap5303=true := by decide +kernel
theorem fusedMap5303_checked : acceptsGraphIso
    (fused (graph core5303) (root 6) 2 6) DegreeTwoThreeSpectrum5144.graph fusedMap5303=true := by decide +kernel
theorem certified5303 : Certified (graph core5303) (root 6) 2 6 :=
  of_native_maps core5303 DegreeTwoThreeSpectrum6869.graph DegreeTwoThreeSpectrum5144.graph
    sourceMap5303 fusedMap5303 sourceMap5303_checked fusedMap5303_checked
    DegreeTwoThreeFiniteComparisons.comparison5303
#print axioms sourceMap5303_checked
#print axioms fusedMap5303_checked
#print axioms certified5303
def sourceMap5303swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,11,1,0,12,13,14,15,16,3,4,5] (sourceLabel 6 6 2 v)
def fusedMap5303swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5303swap_checked : acceptsGraphIso
    (source (graph core5303) (root 6) 6 2) DegreeTwoThreeSpectrum6869.graph sourceMap5303swap=true := by decide +kernel
theorem fusedMap5303swap_checked : acceptsGraphIso
    (fused (graph core5303) (root 6) 6 2) DegreeTwoThreeSpectrum5144.graph fusedMap5303swap=true := by decide +kernel
theorem certified5303swap : Certified (graph core5303) (root 6) 6 2 :=
  of_native_maps core5303 DegreeTwoThreeSpectrum6869.graph DegreeTwoThreeSpectrum5144.graph
    sourceMap5303swap fusedMap5303swap sourceMap5303swap_checked fusedMap5303swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5303
#print axioms sourceMap5303swap_checked
#print axioms fusedMap5303swap_checked
#print axioms certified5303swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
