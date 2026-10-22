/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3275 : Family 9 := level9.get ⟨160,by decide⟩
def sourceMap3275 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3275 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3275_checked : acceptsGraphIso
    (source (graph core3275) (root 9) 0 5) DegreeTwoThreeSpectrum5243.graph sourceMap3275=true := by decide +kernel
theorem fusedMap3275_checked : acceptsGraphIso
    (fused (graph core3275) (root 9) 0 5) DegreeTwoThreeSpectrum5244.graph fusedMap3275=true := by decide +kernel
theorem certified3275 : Certified (graph core3275) (root 9) 0 5 :=
  of_native_maps core3275 DegreeTwoThreeSpectrum5243.graph DegreeTwoThreeSpectrum5244.graph
    sourceMap3275 fusedMap3275 sourceMap3275_checked fusedMap3275_checked
    DegreeTwoThreeFiniteComparisons.comparison3275
#print axioms sourceMap3275_checked
#print axioms fusedMap3275_checked
#print axioms certified3275
def sourceMap3275swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3275swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3275swap_checked : acceptsGraphIso
    (source (graph core3275) (root 9) 5 0) DegreeTwoThreeSpectrum5243.graph sourceMap3275swap=true := by decide +kernel
theorem fusedMap3275swap_checked : acceptsGraphIso
    (fused (graph core3275) (root 9) 5 0) DegreeTwoThreeSpectrum5244.graph fusedMap3275swap=true := by decide +kernel
theorem certified3275swap : Certified (graph core3275) (root 9) 5 0 :=
  of_native_maps core3275 DegreeTwoThreeSpectrum5243.graph DegreeTwoThreeSpectrum5244.graph
    sourceMap3275swap fusedMap3275swap sourceMap3275swap_checked fusedMap3275swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3275
#print axioms sourceMap3275swap_checked
#print axioms fusedMap3275swap_checked
#print axioms certified3275swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
