/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3628 : Family 8 := level8.get ⟨248,by decide⟩
def sourceMap3628 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3628 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3628_checked : acceptsGraphIso
    (source (graph core3628) (root 8) 0 6) DegreeTwoThreeSpectrum6673.graph sourceMap3628=true := by decide +kernel
theorem fusedMap3628_checked : acceptsGraphIso
    (fused (graph core3628) (root 8) 0 6) DegreeTwoThreeSpectrum5540.graph fusedMap3628=true := by decide +kernel
theorem certified3628 : Certified (graph core3628) (root 8) 0 6 :=
  of_native_maps core3628 DegreeTwoThreeSpectrum6673.graph DegreeTwoThreeSpectrum5540.graph
    sourceMap3628 fusedMap3628 sourceMap3628_checked fusedMap3628_checked
    DegreeTwoThreeFiniteComparisons.comparison3628
#print axioms sourceMap3628_checked
#print axioms fusedMap3628_checked
#print axioms certified3628
def sourceMap3628swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3628swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3628swap_checked : acceptsGraphIso
    (source (graph core3628) (root 8) 6 0) DegreeTwoThreeSpectrum6673.graph sourceMap3628swap=true := by decide +kernel
theorem fusedMap3628swap_checked : acceptsGraphIso
    (fused (graph core3628) (root 8) 6 0) DegreeTwoThreeSpectrum5540.graph fusedMap3628swap=true := by decide +kernel
theorem certified3628swap : Certified (graph core3628) (root 8) 6 0 :=
  of_native_maps core3628 DegreeTwoThreeSpectrum6673.graph DegreeTwoThreeSpectrum5540.graph
    sourceMap3628swap fusedMap3628swap sourceMap3628swap_checked fusedMap3628swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3628
#print axioms sourceMap3628swap_checked
#print axioms fusedMap3628swap_checked
#print axioms certified3628swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
