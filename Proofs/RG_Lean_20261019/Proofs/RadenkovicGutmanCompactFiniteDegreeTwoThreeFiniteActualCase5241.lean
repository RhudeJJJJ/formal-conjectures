/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5241 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap5241 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,2,3,4,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5241 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5241_checked : acceptsGraphIso
    (source (graph core5241) (root 6) 2 5) DegreeTwoThreeSpectrum4569.graph sourceMap5241=true := by decide +kernel
theorem fusedMap5241_checked : acceptsGraphIso
    (fused (graph core5241) (root 6) 2 5) DegreeTwoThreeSpectrum3917.graph fusedMap5241=true := by decide +kernel
theorem certified5241 : Certified (graph core5241) (root 6) 2 5 :=
  of_native_maps core5241 DegreeTwoThreeSpectrum4569.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap5241 fusedMap5241 sourceMap5241_checked fusedMap5241_checked
    DegreeTwoThreeFiniteComparisons.comparison5241
#print axioms sourceMap5241_checked
#print axioms fusedMap5241_checked
#print axioms certified5241
def sourceMap5241swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,0,11,12,13,14,15,2,3,4] (sourceLabel 6 5 2 v)
def fusedMap5241swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5241swap_checked : acceptsGraphIso
    (source (graph core5241) (root 6) 5 2) DegreeTwoThreeSpectrum4569.graph sourceMap5241swap=true := by decide +kernel
theorem fusedMap5241swap_checked : acceptsGraphIso
    (fused (graph core5241) (root 6) 5 2) DegreeTwoThreeSpectrum3917.graph fusedMap5241swap=true := by decide +kernel
theorem certified5241swap : Certified (graph core5241) (root 6) 5 2 :=
  of_native_maps core5241 DegreeTwoThreeSpectrum4569.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap5241swap fusedMap5241swap sourceMap5241swap_checked fusedMap5241swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5241
#print axioms sourceMap5241swap_checked
#print axioms fusedMap5241swap_checked
#print axioms certified5241swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
