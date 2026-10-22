/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3029 : Family 10 := level10.get ⟨1635,by decide⟩
def sourceMap3029 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3029 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3029_checked : acceptsGraphIso
    (source (graph core3029) (root 10) 0 4) DegreeTwoThreeSpectrum7190.graph sourceMap3029=true := by decide +kernel
theorem fusedMap3029_checked : acceptsGraphIso
    (fused (graph core3029) (root 10) 0 4) DegreeTwoThreeSpectrum6203.graph fusedMap3029=true := by decide +kernel
theorem certified3029 : Certified (graph core3029) (root 10) 0 4 :=
  of_native_maps core3029 DegreeTwoThreeSpectrum7190.graph DegreeTwoThreeSpectrum6203.graph
    sourceMap3029 fusedMap3029 sourceMap3029_checked fusedMap3029_checked
    DegreeTwoThreeFiniteComparisons.comparison3029
#print axioms sourceMap3029_checked
#print axioms fusedMap3029_checked
#print axioms certified3029
def sourceMap3029swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3029swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3029swap_checked : acceptsGraphIso
    (source (graph core3029) (root 10) 4 0) DegreeTwoThreeSpectrum7190.graph sourceMap3029swap=true := by decide +kernel
theorem fusedMap3029swap_checked : acceptsGraphIso
    (fused (graph core3029) (root 10) 4 0) DegreeTwoThreeSpectrum6203.graph fusedMap3029swap=true := by decide +kernel
theorem certified3029swap : Certified (graph core3029) (root 10) 4 0 :=
  of_native_maps core3029 DegreeTwoThreeSpectrum7190.graph DegreeTwoThreeSpectrum6203.graph
    sourceMap3029swap fusedMap3029swap sourceMap3029swap_checked fusedMap3029swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3029
#print axioms sourceMap3029swap_checked
#print axioms fusedMap3029swap_checked
#print axioms certified3029swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
