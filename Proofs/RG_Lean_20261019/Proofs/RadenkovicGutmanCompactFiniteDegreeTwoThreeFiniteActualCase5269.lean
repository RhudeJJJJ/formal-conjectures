/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5269 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap5269 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5269 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5269_checked : acceptsGraphIso
    (source (graph core5269) (root 7) 2 5) DegreeTwoThreeSpectrum6504.graph sourceMap5269=true := by decide +kernel
theorem fusedMap5269_checked : acceptsGraphIso
    (fused (graph core5269) (root 7) 2 5) DegreeTwoThreeSpectrum5431.graph fusedMap5269=true := by decide +kernel
theorem certified5269 : Certified (graph core5269) (root 7) 2 5 :=
  of_native_maps core5269 DegreeTwoThreeSpectrum6504.graph DegreeTwoThreeSpectrum5431.graph
    sourceMap5269 fusedMap5269 sourceMap5269_checked fusedMap5269_checked
    DegreeTwoThreeFiniteComparisons.comparison5269
#print axioms sourceMap5269_checked
#print axioms fusedMap5269_checked
#print axioms certified5269
def sourceMap5269swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5269swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5269swap_checked : acceptsGraphIso
    (source (graph core5269) (root 7) 5 2) DegreeTwoThreeSpectrum6504.graph sourceMap5269swap=true := by decide +kernel
theorem fusedMap5269swap_checked : acceptsGraphIso
    (fused (graph core5269) (root 7) 5 2) DegreeTwoThreeSpectrum5431.graph fusedMap5269swap=true := by decide +kernel
theorem certified5269swap : Certified (graph core5269) (root 7) 5 2 :=
  of_native_maps core5269 DegreeTwoThreeSpectrum6504.graph DegreeTwoThreeSpectrum5431.graph
    sourceMap5269swap fusedMap5269swap sourceMap5269swap_checked fusedMap5269swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5269
#print axioms sourceMap5269swap_checked
#print axioms fusedMap5269swap_checked
#print axioms certified5269swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
