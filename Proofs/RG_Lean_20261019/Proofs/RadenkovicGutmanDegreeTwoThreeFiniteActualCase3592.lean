/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3592 : Family 8 := level8.get ⟨169,by decide⟩
def sourceMap3592 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3592 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3592_checked : acceptsGraphIso
    (source (graph core3592) (root 8) 0 6) DegreeTwoThreeSpectrum5705.graph sourceMap3592=true := by decide +kernel
theorem fusedMap3592_checked : acceptsGraphIso
    (fused (graph core3592) (root 8) 0 6) DegreeTwoThreeSpectrum5707.graph fusedMap3592=true := by decide +kernel
theorem certified3592 : Certified (graph core3592) (root 8) 0 6 :=
  of_native_maps core3592 DegreeTwoThreeSpectrum5705.graph DegreeTwoThreeSpectrum5707.graph
    sourceMap3592 fusedMap3592 sourceMap3592_checked fusedMap3592_checked
    DegreeTwoThreeFiniteComparisons.comparison3592
#print axioms sourceMap3592_checked
#print axioms fusedMap3592_checked
#print axioms certified3592
def sourceMap3592swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3592swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3592swap_checked : acceptsGraphIso
    (source (graph core3592) (root 8) 6 0) DegreeTwoThreeSpectrum5705.graph sourceMap3592swap=true := by decide +kernel
theorem fusedMap3592swap_checked : acceptsGraphIso
    (fused (graph core3592) (root 8) 6 0) DegreeTwoThreeSpectrum5707.graph fusedMap3592swap=true := by decide +kernel
theorem certified3592swap : Certified (graph core3592) (root 8) 6 0 :=
  of_native_maps core3592 DegreeTwoThreeSpectrum5705.graph DegreeTwoThreeSpectrum5707.graph
    sourceMap3592swap fusedMap3592swap sourceMap3592swap_checked fusedMap3592swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3592
#print axioms sourceMap3592swap_checked
#print axioms fusedMap3592swap_checked
#print axioms certified3592swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
