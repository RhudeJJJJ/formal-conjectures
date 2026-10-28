/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5267 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap5267 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5267 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5267_checked : acceptsGraphIso
    (source (graph core5267) (root 7) 2 5) DegreeTwoThreeSpectrum6347.graph sourceMap5267=true := by decide +kernel
theorem fusedMap5267_checked : acceptsGraphIso
    (fused (graph core5267) (root 7) 2 5) DegreeTwoThreeSpectrum5310.graph fusedMap5267=true := by decide +kernel
theorem certified5267 : Certified (graph core5267) (root 7) 2 5 :=
  of_native_maps core5267 DegreeTwoThreeSpectrum6347.graph DegreeTwoThreeSpectrum5310.graph
    sourceMap5267 fusedMap5267 sourceMap5267_checked fusedMap5267_checked
    DegreeTwoThreeFiniteComparisons.comparison5267
#print axioms sourceMap5267_checked
#print axioms fusedMap5267_checked
#print axioms certified5267
def sourceMap5267swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,12,13,14,15,16,9,10,11] (sourceLabel 7 5 2 v)
def fusedMap5267swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5267swap_checked : acceptsGraphIso
    (source (graph core5267) (root 7) 5 2) DegreeTwoThreeSpectrum6347.graph sourceMap5267swap=true := by decide +kernel
theorem fusedMap5267swap_checked : acceptsGraphIso
    (fused (graph core5267) (root 7) 5 2) DegreeTwoThreeSpectrum5310.graph fusedMap5267swap=true := by decide +kernel
theorem certified5267swap : Certified (graph core5267) (root 7) 5 2 :=
  of_native_maps core5267 DegreeTwoThreeSpectrum6347.graph DegreeTwoThreeSpectrum5310.graph
    sourceMap5267swap fusedMap5267swap sourceMap5267swap_checked fusedMap5267swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5267
#print axioms sourceMap5267swap_checked
#print axioms fusedMap5267swap_checked
#print axioms certified5267swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
