/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanNoRuntimeComparison3296OriginalNamespace
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3296 : Family 9 := level9.get ⟨224,by decide⟩
def sourceMap3296 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3296 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3296_checked : acceptsGraphIso
    (source (graph core3296) (root 9) 0 5) DegreeTwoThreeSpectrum5531.graph sourceMap3296=true := by decide +kernel
theorem fusedMap3296_checked : acceptsGraphIso
    (fused (graph core3296) (root 9) 0 5) DegreeTwoThreeSpectrum5532.graph fusedMap3296=true := by decide +kernel
theorem certified3296 : Certified (graph core3296) (root 9) 0 5 :=
  of_native_maps core3296 DegreeTwoThreeSpectrum5531.graph DegreeTwoThreeSpectrum5532.graph
    sourceMap3296 fusedMap3296 sourceMap3296_checked fusedMap3296_checked
    DegreeTwoThreeFiniteComparisons.comparison3296
#print axioms sourceMap3296_checked
#print axioms fusedMap3296_checked
#print axioms certified3296
def sourceMap3296swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3296swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3296swap_checked : acceptsGraphIso
    (source (graph core3296) (root 9) 5 0) DegreeTwoThreeSpectrum5531.graph sourceMap3296swap=true := by decide +kernel
theorem fusedMap3296swap_checked : acceptsGraphIso
    (fused (graph core3296) (root 9) 5 0) DegreeTwoThreeSpectrum5532.graph fusedMap3296swap=true := by decide +kernel
theorem certified3296swap : Certified (graph core3296) (root 9) 5 0 :=
  of_native_maps core3296 DegreeTwoThreeSpectrum5531.graph DegreeTwoThreeSpectrum5532.graph
    sourceMap3296swap fusedMap3296swap sourceMap3296swap_checked fusedMap3296swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3296
#print axioms sourceMap3296swap_checked
#print axioms fusedMap3296swap_checked
#print axioms certified3296swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
