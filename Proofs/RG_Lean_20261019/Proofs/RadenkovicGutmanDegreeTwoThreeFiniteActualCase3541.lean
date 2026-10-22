/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3541 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap3541 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3541 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3541_checked : acceptsGraphIso
    (source (graph core3541) (root 8) 0 6) DegreeTwoThreeSpectrum5040.graph sourceMap3541=true := by decide +kernel
theorem fusedMap3541_checked : acceptsGraphIso
    (fused (graph core3541) (root 8) 0 6) DegreeTwoThreeSpectrum5042.graph fusedMap3541=true := by decide +kernel
theorem certified3541 : Certified (graph core3541) (root 8) 0 6 :=
  of_native_maps core3541 DegreeTwoThreeSpectrum5040.graph DegreeTwoThreeSpectrum5042.graph
    sourceMap3541 fusedMap3541 sourceMap3541_checked fusedMap3541_checked
    DegreeTwoThreeFiniteComparisons.comparison3541
#print axioms sourceMap3541_checked
#print axioms fusedMap3541_checked
#print axioms certified3541
def sourceMap3541swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,9] (sourceLabel 8 6 0 v)
def fusedMap3541swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3541swap_checked : acceptsGraphIso
    (source (graph core3541) (root 8) 6 0) DegreeTwoThreeSpectrum5040.graph sourceMap3541swap=true := by decide +kernel
theorem fusedMap3541swap_checked : acceptsGraphIso
    (fused (graph core3541) (root 8) 6 0) DegreeTwoThreeSpectrum5042.graph fusedMap3541swap=true := by decide +kernel
theorem certified3541swap : Certified (graph core3541) (root 8) 6 0 :=
  of_native_maps core3541 DegreeTwoThreeSpectrum5040.graph DegreeTwoThreeSpectrum5042.graph
    sourceMap3541swap fusedMap3541swap sourceMap3541swap_checked fusedMap3541swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3541
#print axioms sourceMap3541swap_checked
#print axioms fusedMap3541swap_checked
#print axioms certified3541swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
