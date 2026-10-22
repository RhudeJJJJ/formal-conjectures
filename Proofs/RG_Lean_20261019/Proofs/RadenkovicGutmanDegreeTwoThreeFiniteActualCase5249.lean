/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5249 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap5249 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5249 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5249_checked : acceptsGraphIso
    (source (graph core5249) (root 7) 2 5) DegreeTwoThreeSpectrum6322.graph sourceMap5249=true := by decide +kernel
theorem fusedMap5249_checked : acceptsGraphIso
    (fused (graph core5249) (root 7) 2 5) DegreeTwoThreeSpectrum4976.graph fusedMap5249=true := by decide +kernel
theorem certified5249 : Certified (graph core5249) (root 7) 2 5 :=
  of_native_maps core5249 DegreeTwoThreeSpectrum6322.graph DegreeTwoThreeSpectrum4976.graph
    sourceMap5249 fusedMap5249 sourceMap5249_checked fusedMap5249_checked
    DegreeTwoThreeFiniteComparisons.comparison5249
#print axioms sourceMap5249_checked
#print axioms fusedMap5249_checked
#print axioms certified5249
def sourceMap5249swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5249swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5249swap_checked : acceptsGraphIso
    (source (graph core5249) (root 7) 5 2) DegreeTwoThreeSpectrum6322.graph sourceMap5249swap=true := by decide +kernel
theorem fusedMap5249swap_checked : acceptsGraphIso
    (fused (graph core5249) (root 7) 5 2) DegreeTwoThreeSpectrum4976.graph fusedMap5249swap=true := by decide +kernel
theorem certified5249swap : Certified (graph core5249) (root 7) 5 2 :=
  of_native_maps core5249 DegreeTwoThreeSpectrum6322.graph DegreeTwoThreeSpectrum4976.graph
    sourceMap5249swap fusedMap5249swap sourceMap5249swap_checked fusedMap5249swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5249
#print axioms sourceMap5249swap_checked
#print axioms fusedMap5249swap_checked
#print axioms certified5249swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
