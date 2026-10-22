/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3033 : Family 10 := level10.get ⟨1647,by decide⟩
def sourceMap3033 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3033 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3033_checked : acceptsGraphIso
    (source (graph core3033) (root 10) 0 4) DegreeTwoThreeSpectrum7207.graph sourceMap3033=true := by decide +kernel
theorem fusedMap3033_checked : acceptsGraphIso
    (fused (graph core3033) (root 10) 0 4) DegreeTwoThreeSpectrum6237.graph fusedMap3033=true := by decide +kernel
theorem certified3033 : Certified (graph core3033) (root 10) 0 4 :=
  of_native_maps core3033 DegreeTwoThreeSpectrum7207.graph DegreeTwoThreeSpectrum6237.graph
    sourceMap3033 fusedMap3033 sourceMap3033_checked fusedMap3033_checked
    DegreeTwoThreeFiniteComparisons.comparison3033
#print axioms sourceMap3033_checked
#print axioms fusedMap3033_checked
#print axioms certified3033
def sourceMap3033swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3033swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3033swap_checked : acceptsGraphIso
    (source (graph core3033) (root 10) 4 0) DegreeTwoThreeSpectrum7207.graph sourceMap3033swap=true := by decide +kernel
theorem fusedMap3033swap_checked : acceptsGraphIso
    (fused (graph core3033) (root 10) 4 0) DegreeTwoThreeSpectrum6237.graph fusedMap3033swap=true := by decide +kernel
theorem certified3033swap : Certified (graph core3033) (root 10) 4 0 :=
  of_native_maps core3033 DegreeTwoThreeSpectrum7207.graph DegreeTwoThreeSpectrum6237.graph
    sourceMap3033swap fusedMap3033swap sourceMap3033swap_checked fusedMap3033swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3033
#print axioms sourceMap3033swap_checked
#print axioms fusedMap3033swap_checked
#print axioms certified3033swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
