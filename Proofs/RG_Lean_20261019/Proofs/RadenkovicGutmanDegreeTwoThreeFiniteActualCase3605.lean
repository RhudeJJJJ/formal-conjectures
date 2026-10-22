/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3605 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap3605 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3605 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3605_checked : acceptsGraphIso
    (source (graph core3605) (root 8) 0 6) DegreeTwoThreeSpectrum6083.graph sourceMap3605=true := by decide +kernel
theorem fusedMap3605_checked : acceptsGraphIso
    (fused (graph core3605) (root 8) 0 6) DegreeTwoThreeSpectrum5165.graph fusedMap3605=true := by decide +kernel
theorem certified3605 : Certified (graph core3605) (root 8) 0 6 :=
  of_native_maps core3605 DegreeTwoThreeSpectrum6083.graph DegreeTwoThreeSpectrum5165.graph
    sourceMap3605 fusedMap3605 sourceMap3605_checked fusedMap3605_checked
    DegreeTwoThreeFiniteComparisons.comparison3605
#print axioms sourceMap3605_checked
#print axioms fusedMap3605_checked
#print axioms certified3605
def sourceMap3605swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3605swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3605swap_checked : acceptsGraphIso
    (source (graph core3605) (root 8) 6 0) DegreeTwoThreeSpectrum6083.graph sourceMap3605swap=true := by decide +kernel
theorem fusedMap3605swap_checked : acceptsGraphIso
    (fused (graph core3605) (root 8) 6 0) DegreeTwoThreeSpectrum5165.graph fusedMap3605swap=true := by decide +kernel
theorem certified3605swap : Certified (graph core3605) (root 8) 6 0 :=
  of_native_maps core3605 DegreeTwoThreeSpectrum6083.graph DegreeTwoThreeSpectrum5165.graph
    sourceMap3605swap fusedMap3605swap sourceMap3605swap_checked fusedMap3605swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3605
#print axioms sourceMap3605swap_checked
#print axioms fusedMap3605swap_checked
#print axioms certified3605swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
