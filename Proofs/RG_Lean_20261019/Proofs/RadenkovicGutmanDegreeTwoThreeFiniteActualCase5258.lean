/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5258 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap5258 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5258 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5258_checked : acceptsGraphIso
    (source (graph core5258) (root 7) 2 5) DegreeTwoThreeSpectrum6975.graph sourceMap5258=true := by decide +kernel
theorem fusedMap5258_checked : acceptsGraphIso
    (fused (graph core5258) (root 7) 2 5) DegreeTwoThreeSpectrum5061.graph fusedMap5258=true := by decide +kernel
theorem certified5258 : Certified (graph core5258) (root 7) 2 5 :=
  of_native_maps core5258 DegreeTwoThreeSpectrum6975.graph DegreeTwoThreeSpectrum5061.graph
    sourceMap5258 fusedMap5258 sourceMap5258_checked fusedMap5258_checked
    DegreeTwoThreeFiniteComparisons.comparison5258
#print axioms sourceMap5258_checked
#print axioms fusedMap5258_checked
#print axioms certified5258
def sourceMap5258swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5258swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5258swap_checked : acceptsGraphIso
    (source (graph core5258) (root 7) 5 2) DegreeTwoThreeSpectrum6975.graph sourceMap5258swap=true := by decide +kernel
theorem fusedMap5258swap_checked : acceptsGraphIso
    (fused (graph core5258) (root 7) 5 2) DegreeTwoThreeSpectrum5061.graph fusedMap5258swap=true := by decide +kernel
theorem certified5258swap : Certified (graph core5258) (root 7) 5 2 :=
  of_native_maps core5258 DegreeTwoThreeSpectrum6975.graph DegreeTwoThreeSpectrum5061.graph
    sourceMap5258swap fusedMap5258swap sourceMap5258swap_checked fusedMap5258swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5258
#print axioms sourceMap5258swap_checked
#print axioms fusedMap5258swap_checked
#print axioms certified5258swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
