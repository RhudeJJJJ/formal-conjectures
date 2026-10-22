/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3254 : Family 9 := level9.get ⟨90,by decide⟩
def sourceMap3254 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3254 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3254_checked : acceptsGraphIso
    (source (graph core3254) (root 9) 0 5) DegreeTwoThreeSpectrum5646.graph sourceMap3254=true := by decide +kernel
theorem fusedMap3254_checked : acceptsGraphIso
    (fused (graph core3254) (root 9) 0 5) DegreeTwoThreeSpectrum5036.graph fusedMap3254=true := by decide +kernel
theorem certified3254 : Certified (graph core3254) (root 9) 0 5 :=
  of_native_maps core3254 DegreeTwoThreeSpectrum5646.graph DegreeTwoThreeSpectrum5036.graph
    sourceMap3254 fusedMap3254 sourceMap3254_checked fusedMap3254_checked
    DegreeTwoThreeFiniteComparisons.comparison3254
#print axioms sourceMap3254_checked
#print axioms fusedMap3254_checked
#print axioms certified3254
def sourceMap3254swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3254swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3254swap_checked : acceptsGraphIso
    (source (graph core3254) (root 9) 5 0) DegreeTwoThreeSpectrum5646.graph sourceMap3254swap=true := by decide +kernel
theorem fusedMap3254swap_checked : acceptsGraphIso
    (fused (graph core3254) (root 9) 5 0) DegreeTwoThreeSpectrum5036.graph fusedMap3254swap=true := by decide +kernel
theorem certified3254swap : Certified (graph core3254) (root 9) 5 0 :=
  of_native_maps core3254 DegreeTwoThreeSpectrum5646.graph DegreeTwoThreeSpectrum5036.graph
    sourceMap3254swap fusedMap3254swap sourceMap3254swap_checked fusedMap3254swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3254
#print axioms sourceMap3254swap_checked
#print axioms fusedMap3254swap_checked
#print axioms certified3254swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
