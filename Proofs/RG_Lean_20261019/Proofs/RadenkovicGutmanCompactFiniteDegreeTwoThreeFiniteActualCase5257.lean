/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5257 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap5257 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5257 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5257_checked : acceptsGraphIso
    (source (graph core5257) (root 7) 2 5) DegreeTwoThreeSpectrum6951.graph sourceMap5257=true := by decide +kernel
theorem fusedMap5257_checked : acceptsGraphIso
    (fused (graph core5257) (root 7) 2 5) DegreeTwoThreeSpectrum5056.graph fusedMap5257=true := by decide +kernel
theorem certified5257 : Certified (graph core5257) (root 7) 2 5 :=
  of_native_maps core5257 DegreeTwoThreeSpectrum6951.graph DegreeTwoThreeSpectrum5056.graph
    sourceMap5257 fusedMap5257 sourceMap5257_checked fusedMap5257_checked
    DegreeTwoThreeFiniteComparisons.comparison5257
#print axioms sourceMap5257_checked
#print axioms fusedMap5257_checked
#print axioms certified5257
def sourceMap5257swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5257swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5257swap_checked : acceptsGraphIso
    (source (graph core5257) (root 7) 5 2) DegreeTwoThreeSpectrum6951.graph sourceMap5257swap=true := by decide +kernel
theorem fusedMap5257swap_checked : acceptsGraphIso
    (fused (graph core5257) (root 7) 5 2) DegreeTwoThreeSpectrum5056.graph fusedMap5257swap=true := by decide +kernel
theorem certified5257swap : Certified (graph core5257) (root 7) 5 2 :=
  of_native_maps core5257 DegreeTwoThreeSpectrum6951.graph DegreeTwoThreeSpectrum5056.graph
    sourceMap5257swap fusedMap5257swap sourceMap5257swap_checked fusedMap5257swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5257
#print axioms sourceMap5257swap_checked
#print axioms fusedMap5257swap_checked
#print axioms certified5257swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
