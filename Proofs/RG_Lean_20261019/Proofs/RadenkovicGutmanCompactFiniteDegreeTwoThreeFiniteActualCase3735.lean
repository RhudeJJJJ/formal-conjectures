/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3735 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3735 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (sourceLabel 5 0 9 v)
def fusedMap3735 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 0 9 v)
theorem sourceMap3735_checked : acceptsGraphIso
    (source (graph core3735) (root 5) 0 9) DegreeTwoThreeSpectrum5168.graph sourceMap3735=true := by decide +kernel
theorem fusedMap3735_checked : acceptsGraphIso
    (fused (graph core3735) (root 5) 0 9) DegreeTwoThreeSpectrum4966.graph fusedMap3735=true := by decide +kernel
theorem certified3735 : Certified (graph core3735) (root 5) 0 9 :=
  of_native_maps core3735 DegreeTwoThreeSpectrum5168.graph DegreeTwoThreeSpectrum4966.graph
    sourceMap3735 fusedMap3735 sourceMap3735_checked fusedMap3735_checked
    DegreeTwoThreeFiniteComparisons.comparison3735
#print axioms sourceMap3735_checked
#print axioms fusedMap3735_checked
#print axioms certified3735
def sourceMap3735swap : (Vertices 5 ⊕ Fin 10 ⊕ Fin 1) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,11,12,13,14,15,16,10] (sourceLabel 5 9 0 v)
def fusedMap3735swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 9 0 v)
theorem sourceMap3735swap_checked : acceptsGraphIso
    (source (graph core3735) (root 5) 9 0) DegreeTwoThreeSpectrum5168.graph sourceMap3735swap=true := by decide +kernel
theorem fusedMap3735swap_checked : acceptsGraphIso
    (fused (graph core3735) (root 5) 9 0) DegreeTwoThreeSpectrum4966.graph fusedMap3735swap=true := by decide +kernel
theorem certified3735swap : Certified (graph core3735) (root 5) 9 0 :=
  of_native_maps core3735 DegreeTwoThreeSpectrum5168.graph DegreeTwoThreeSpectrum4966.graph
    sourceMap3735swap fusedMap3735swap sourceMap3735swap_checked fusedMap3735swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3735
#print axioms sourceMap3735swap_checked
#print axioms fusedMap3735swap_checked
#print axioms certified3735swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
