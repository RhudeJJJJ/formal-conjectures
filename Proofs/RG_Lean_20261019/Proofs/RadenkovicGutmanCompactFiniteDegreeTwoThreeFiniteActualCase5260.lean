/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5260 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap5260 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,6,7,8,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5260 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5260_checked : acceptsGraphIso
    (source (graph core5260) (root 7) 2 5) DegreeTwoThreeSpectrum7018.graph sourceMap5260=true := by decide +kernel
theorem fusedMap5260_checked : acceptsGraphIso
    (fused (graph core5260) (root 7) 2 5) DegreeTwoThreeSpectrum5082.graph fusedMap5260=true := by decide +kernel
theorem certified5260 : Certified (graph core5260) (root 7) 2 5 :=
  of_native_maps core5260 DegreeTwoThreeSpectrum7018.graph DegreeTwoThreeSpectrum5082.graph
    sourceMap5260 fusedMap5260 sourceMap5260_checked fusedMap5260_checked
    DegreeTwoThreeFiniteComparisons.comparison5260
#print axioms sourceMap5260_checked
#print axioms fusedMap5260_checked
#print axioms certified5260
def sourceMap5260swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,0,12,13,14,15,16,6,7,8] (sourceLabel 7 5 2 v)
def fusedMap5260swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5260swap_checked : acceptsGraphIso
    (source (graph core5260) (root 7) 5 2) DegreeTwoThreeSpectrum7018.graph sourceMap5260swap=true := by decide +kernel
theorem fusedMap5260swap_checked : acceptsGraphIso
    (fused (graph core5260) (root 7) 5 2) DegreeTwoThreeSpectrum5082.graph fusedMap5260swap=true := by decide +kernel
theorem certified5260swap : Certified (graph core5260) (root 7) 5 2 :=
  of_native_maps core5260 DegreeTwoThreeSpectrum7018.graph DegreeTwoThreeSpectrum5082.graph
    sourceMap5260swap fusedMap5260swap sourceMap5260swap_checked fusedMap5260swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5260
#print axioms sourceMap5260swap_checked
#print axioms fusedMap5260swap_checked
#print axioms certified5260swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
