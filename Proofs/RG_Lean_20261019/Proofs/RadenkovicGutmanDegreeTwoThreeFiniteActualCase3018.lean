/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3018 : Family 10 := level10.get ⟨1607,by decide⟩
def sourceMap3018 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3018 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3018_checked : acceptsGraphIso
    (source (graph core3018) (root 10) 0 4) DegreeTwoThreeSpectrum7153.graph sourceMap3018=true := by decide +kernel
theorem fusedMap3018_checked : acceptsGraphIso
    (fused (graph core3018) (root 10) 0 4) DegreeTwoThreeSpectrum6126.graph fusedMap3018=true := by decide +kernel
theorem certified3018 : Certified (graph core3018) (root 10) 0 4 :=
  of_native_maps core3018 DegreeTwoThreeSpectrum7153.graph DegreeTwoThreeSpectrum6126.graph
    sourceMap3018 fusedMap3018 sourceMap3018_checked fusedMap3018_checked
    DegreeTwoThreeFiniteComparisons.comparison3018
#print axioms sourceMap3018_checked
#print axioms fusedMap3018_checked
#print axioms certified3018
def sourceMap3018swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3018swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3018swap_checked : acceptsGraphIso
    (source (graph core3018) (root 10) 4 0) DegreeTwoThreeSpectrum7153.graph sourceMap3018swap=true := by decide +kernel
theorem fusedMap3018swap_checked : acceptsGraphIso
    (fused (graph core3018) (root 10) 4 0) DegreeTwoThreeSpectrum6126.graph fusedMap3018swap=true := by decide +kernel
theorem certified3018swap : Certified (graph core3018) (root 10) 4 0 :=
  of_native_maps core3018 DegreeTwoThreeSpectrum7153.graph DegreeTwoThreeSpectrum6126.graph
    sourceMap3018swap fusedMap3018swap sourceMap3018swap_checked fusedMap3018swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3018
#print axioms sourceMap3018swap_checked
#print axioms fusedMap3018swap_checked
#print axioms certified3018swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
