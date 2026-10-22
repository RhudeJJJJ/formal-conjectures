/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3420 : Family 9 := level9.get ⟨544,by decide⟩
def sourceMap3420 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3420 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3420_checked : acceptsGraphIso
    (source (graph core3420) (root 9) 0 5) DegreeTwoThreeSpectrum5967.graph sourceMap3420=true := by decide +kernel
theorem fusedMap3420_checked : acceptsGraphIso
    (fused (graph core3420) (root 9) 0 5) DegreeTwoThreeSpectrum5968.graph fusedMap3420=true := by decide +kernel
theorem certified3420 : Certified (graph core3420) (root 9) 0 5 :=
  of_native_maps core3420 DegreeTwoThreeSpectrum5967.graph DegreeTwoThreeSpectrum5968.graph
    sourceMap3420 fusedMap3420 sourceMap3420_checked fusedMap3420_checked
    DegreeTwoThreeFiniteComparisons.comparison3420
#print axioms sourceMap3420_checked
#print axioms fusedMap3420_checked
#print axioms certified3420
def sourceMap3420swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3420swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3420swap_checked : acceptsGraphIso
    (source (graph core3420) (root 9) 5 0) DegreeTwoThreeSpectrum5967.graph sourceMap3420swap=true := by decide +kernel
theorem fusedMap3420swap_checked : acceptsGraphIso
    (fused (graph core3420) (root 9) 5 0) DegreeTwoThreeSpectrum5968.graph fusedMap3420swap=true := by decide +kernel
theorem certified3420swap : Certified (graph core3420) (root 9) 5 0 :=
  of_native_maps core3420 DegreeTwoThreeSpectrum5967.graph DegreeTwoThreeSpectrum5968.graph
    sourceMap3420swap fusedMap3420swap sourceMap3420swap_checked fusedMap3420swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3420
#print axioms sourceMap3420swap_checked
#print axioms fusedMap3420swap_checked
#print axioms certified3420swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
