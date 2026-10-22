/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3451 : Family 9 := level9.get ⟨611,by decide⟩
def sourceMap3451 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3451 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3451_checked : acceptsGraphIso
    (source (graph core3451) (root 9) 0 5) DegreeTwoThreeSpectrum6290.graph sourceMap3451=true := by decide +kernel
theorem fusedMap3451_checked : acceptsGraphIso
    (fused (graph core3451) (root 9) 0 5) DegreeTwoThreeSpectrum6291.graph fusedMap3451=true := by decide +kernel
theorem certified3451 : Certified (graph core3451) (root 9) 0 5 :=
  of_native_maps core3451 DegreeTwoThreeSpectrum6290.graph DegreeTwoThreeSpectrum6291.graph
    sourceMap3451 fusedMap3451 sourceMap3451_checked fusedMap3451_checked
    DegreeTwoThreeFiniteComparisons.comparison3451
#print axioms sourceMap3451_checked
#print axioms fusedMap3451_checked
#print axioms certified3451
def sourceMap3451swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3451swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3451swap_checked : acceptsGraphIso
    (source (graph core3451) (root 9) 5 0) DegreeTwoThreeSpectrum6290.graph sourceMap3451swap=true := by decide +kernel
theorem fusedMap3451swap_checked : acceptsGraphIso
    (fused (graph core3451) (root 9) 5 0) DegreeTwoThreeSpectrum6291.graph fusedMap3451swap=true := by decide +kernel
theorem certified3451swap : Certified (graph core3451) (root 9) 5 0 :=
  of_native_maps core3451 DegreeTwoThreeSpectrum6290.graph DegreeTwoThreeSpectrum6291.graph
    sourceMap3451swap fusedMap3451swap sourceMap3451swap_checked fusedMap3451swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3451
#print axioms sourceMap3451swap_checked
#print axioms fusedMap3451swap_checked
#print axioms certified3451swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
