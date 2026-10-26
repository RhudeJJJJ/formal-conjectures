/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3674 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap3674 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3674 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3674_checked : acceptsGraphIso
    (source (graph core3674) (root 7) 0 7) DegreeTwoThreeSpectrum5579.graph sourceMap3674=true := by decide +kernel
theorem fusedMap3674_checked : acceptsGraphIso
    (fused (graph core3674) (root 7) 0 7) DegreeTwoThreeSpectrum5023.graph fusedMap3674=true := by decide +kernel
theorem certified3674 : Certified (graph core3674) (root 7) 0 7 :=
  of_native_maps core3674 DegreeTwoThreeSpectrum5579.graph DegreeTwoThreeSpectrum5023.graph
    sourceMap3674 fusedMap3674 sourceMap3674_checked fusedMap3674_checked
    DegreeTwoThreeFiniteComparisons.comparison3674
#print axioms sourceMap3674_checked
#print axioms fusedMap3674_checked
#print axioms certified3674
def sourceMap3674swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3674swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3674swap_checked : acceptsGraphIso
    (source (graph core3674) (root 7) 7 0) DegreeTwoThreeSpectrum5579.graph sourceMap3674swap=true := by decide +kernel
theorem fusedMap3674swap_checked : acceptsGraphIso
    (fused (graph core3674) (root 7) 7 0) DegreeTwoThreeSpectrum5023.graph fusedMap3674swap=true := by decide +kernel
theorem certified3674swap : Certified (graph core3674) (root 7) 7 0 :=
  of_native_maps core3674 DegreeTwoThreeSpectrum5579.graph DegreeTwoThreeSpectrum5023.graph
    sourceMap3674swap fusedMap3674swap sourceMap3674swap_checked fusedMap3674swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3674
#print axioms sourceMap3674swap_checked
#print axioms fusedMap3674swap_checked
#print axioms certified3674swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
