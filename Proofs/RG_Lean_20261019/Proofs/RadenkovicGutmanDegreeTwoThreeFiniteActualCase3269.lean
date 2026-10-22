/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3269 : Family 9 := level9.get ⟨134,by decide⟩
def sourceMap3269 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 9 0 5 v)
def fusedMap3269 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3269_checked : acceptsGraphIso
    (source (graph core3269) (root 9) 0 5) DegreeTwoThreeSpectrum5958.graph sourceMap3269=true := by decide +kernel
theorem fusedMap3269_checked : acceptsGraphIso
    (fused (graph core3269) (root 9) 0 5) DegreeTwoThreeSpectrum5125.graph fusedMap3269=true := by decide +kernel
theorem certified3269 : Certified (graph core3269) (root 9) 0 5 :=
  of_native_maps core3269 DegreeTwoThreeSpectrum5958.graph DegreeTwoThreeSpectrum5125.graph
    sourceMap3269 fusedMap3269 sourceMap3269_checked fusedMap3269_checked
    DegreeTwoThreeFiniteComparisons.comparison3269
#print axioms sourceMap3269_checked
#print axioms fusedMap3269_checked
#print axioms certified3269
def sourceMap3269swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12,16] (sourceLabel 9 5 0 v)
def fusedMap3269swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3269swap_checked : acceptsGraphIso
    (source (graph core3269) (root 9) 5 0) DegreeTwoThreeSpectrum5958.graph sourceMap3269swap=true := by decide +kernel
theorem fusedMap3269swap_checked : acceptsGraphIso
    (fused (graph core3269) (root 9) 5 0) DegreeTwoThreeSpectrum5125.graph fusedMap3269swap=true := by decide +kernel
theorem certified3269swap : Certified (graph core3269) (root 9) 5 0 :=
  of_native_maps core3269 DegreeTwoThreeSpectrum5958.graph DegreeTwoThreeSpectrum5125.graph
    sourceMap3269swap fusedMap3269swap sourceMap3269swap_checked fusedMap3269swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3269
#print axioms sourceMap3269swap_checked
#print axioms fusedMap3269swap_checked
#print axioms certified3269swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
