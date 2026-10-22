/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5268 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap5268 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,6,7,8,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5268 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5268_checked : acceptsGraphIso
    (source (graph core5268) (root 7) 2 5) DegreeTwoThreeSpectrum6348.graph sourceMap5268=true := by decide +kernel
theorem fusedMap5268_checked : acceptsGraphIso
    (fused (graph core5268) (root 7) 2 5) DegreeTwoThreeSpectrum5315.graph fusedMap5268=true := by decide +kernel
theorem certified5268 : Certified (graph core5268) (root 7) 2 5 :=
  of_native_maps core5268 DegreeTwoThreeSpectrum6348.graph DegreeTwoThreeSpectrum5315.graph
    sourceMap5268 fusedMap5268 sourceMap5268_checked fusedMap5268_checked
    DegreeTwoThreeFiniteComparisons.comparison5268
#print axioms sourceMap5268_checked
#print axioms fusedMap5268_checked
#print axioms certified5268
def sourceMap5268swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,0,12,13,14,15,16,6,7,8] (sourceLabel 7 5 2 v)
def fusedMap5268swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5268swap_checked : acceptsGraphIso
    (source (graph core5268) (root 7) 5 2) DegreeTwoThreeSpectrum6348.graph sourceMap5268swap=true := by decide +kernel
theorem fusedMap5268swap_checked : acceptsGraphIso
    (fused (graph core5268) (root 7) 5 2) DegreeTwoThreeSpectrum5315.graph fusedMap5268swap=true := by decide +kernel
theorem certified5268swap : Certified (graph core5268) (root 7) 5 2 :=
  of_native_maps core5268 DegreeTwoThreeSpectrum6348.graph DegreeTwoThreeSpectrum5315.graph
    sourceMap5268swap fusedMap5268swap sourceMap5268swap_checked fusedMap5268swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5268
#print axioms sourceMap5268swap_checked
#print axioms fusedMap5268swap_checked
#print axioms certified5268swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
