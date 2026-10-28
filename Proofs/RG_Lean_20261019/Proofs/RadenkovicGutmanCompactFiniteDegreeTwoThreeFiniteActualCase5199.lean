/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5199 : Family 8 := level8.get ⟨231,by decide⟩
def sourceMap5199 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5199 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5199_checked : acceptsGraphIso
    (source (graph core5199) (root 8) 2 4) DegreeTwoThreeSpectrum7326.graph sourceMap5199=true := by decide +kernel
theorem fusedMap5199_checked : acceptsGraphIso
    (fused (graph core5199) (root 8) 2 4) DegreeTwoThreeSpectrum5421.graph fusedMap5199=true := by decide +kernel
theorem certified5199 : Certified (graph core5199) (root 8) 2 4 :=
  of_native_maps core5199 DegreeTwoThreeSpectrum7326.graph DegreeTwoThreeSpectrum5421.graph
    sourceMap5199 fusedMap5199 sourceMap5199_checked fusedMap5199_checked
    DegreeTwoThreeFiniteComparisons.comparison5199
#print axioms sourceMap5199_checked
#print axioms fusedMap5199_checked
#print axioms certified5199
def sourceMap5199swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5199swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5199swap_checked : acceptsGraphIso
    (source (graph core5199) (root 8) 4 2) DegreeTwoThreeSpectrum7326.graph sourceMap5199swap=true := by decide +kernel
theorem fusedMap5199swap_checked : acceptsGraphIso
    (fused (graph core5199) (root 8) 4 2) DegreeTwoThreeSpectrum5421.graph fusedMap5199swap=true := by decide +kernel
theorem certified5199swap : Certified (graph core5199) (root 8) 4 2 :=
  of_native_maps core5199 DegreeTwoThreeSpectrum7326.graph DegreeTwoThreeSpectrum5421.graph
    sourceMap5199swap fusedMap5199swap sourceMap5199swap_checked fusedMap5199swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5199
#print axioms sourceMap5199swap_checked
#print axioms fusedMap5199swap_checked
#print axioms certified5199swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
