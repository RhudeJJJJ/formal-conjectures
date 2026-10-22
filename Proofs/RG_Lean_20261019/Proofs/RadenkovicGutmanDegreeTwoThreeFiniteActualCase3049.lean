/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3049 : Family 10 := level10.get ⟨1703,by decide⟩
def sourceMap3049 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3049 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3049_checked : acceptsGraphIso
    (source (graph core3049) (root 10) 0 4) DegreeTwoThreeSpectrum7324.graph sourceMap3049=true := by decide +kernel
theorem fusedMap3049_checked : acceptsGraphIso
    (fused (graph core3049) (root 10) 0 4) DegreeTwoThreeSpectrum6470.graph fusedMap3049=true := by decide +kernel
theorem certified3049 : Certified (graph core3049) (root 10) 0 4 :=
  of_native_maps core3049 DegreeTwoThreeSpectrum7324.graph DegreeTwoThreeSpectrum6470.graph
    sourceMap3049 fusedMap3049 sourceMap3049_checked fusedMap3049_checked
    DegreeTwoThreeFiniteComparisons.comparison3049
#print axioms sourceMap3049_checked
#print axioms fusedMap3049_checked
#print axioms certified3049
def sourceMap3049swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3049swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3049swap_checked : acceptsGraphIso
    (source (graph core3049) (root 10) 4 0) DegreeTwoThreeSpectrum7324.graph sourceMap3049swap=true := by decide +kernel
theorem fusedMap3049swap_checked : acceptsGraphIso
    (fused (graph core3049) (root 10) 4 0) DegreeTwoThreeSpectrum6470.graph fusedMap3049swap=true := by decide +kernel
theorem certified3049swap : Certified (graph core3049) (root 10) 4 0 :=
  of_native_maps core3049 DegreeTwoThreeSpectrum7324.graph DegreeTwoThreeSpectrum6470.graph
    sourceMap3049swap fusedMap3049swap sourceMap3049swap_checked fusedMap3049swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3049
#print axioms sourceMap3049swap_checked
#print axioms fusedMap3049swap_checked
#print axioms certified3049swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
