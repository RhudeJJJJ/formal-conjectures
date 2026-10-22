/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3093 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap3093 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3093 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3093_checked : acceptsGraphIso
    (source (graph core3093) (root 6) 0 5) DegreeTwoThreeSpectrum1766.graph sourceMap3093=true := by decide +kernel
theorem fusedMap3093_checked : acceptsGraphIso
    (fused (graph core3093) (root 6) 0 5) DegreeTwoThreeSpectrum1768.graph fusedMap3093=true := by decide +kernel
theorem certified3093 : Certified (graph core3093) (root 6) 0 5 :=
  of_native_maps core3093 DegreeTwoThreeSpectrum1766.graph DegreeTwoThreeSpectrum1768.graph
    sourceMap3093 fusedMap3093 sourceMap3093_checked fusedMap3093_checked
    DegreeTwoThreeFiniteComparisons.comparison3093
#print axioms sourceMap3093_checked
#print axioms fusedMap3093_checked
#print axioms certified3093
def sourceMap3093swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3093swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3093swap_checked : acceptsGraphIso
    (source (graph core3093) (root 6) 5 0) DegreeTwoThreeSpectrum1766.graph sourceMap3093swap=true := by decide +kernel
theorem fusedMap3093swap_checked : acceptsGraphIso
    (fused (graph core3093) (root 6) 5 0) DegreeTwoThreeSpectrum1768.graph fusedMap3093swap=true := by decide +kernel
theorem certified3093swap : Certified (graph core3093) (root 6) 5 0 :=
  of_native_maps core3093 DegreeTwoThreeSpectrum1766.graph DegreeTwoThreeSpectrum1768.graph
    sourceMap3093swap fusedMap3093swap sourceMap3093swap_checked fusedMap3093swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3093
#print axioms sourceMap3093swap_checked
#print axioms fusedMap3093swap_checked
#print axioms certified3093swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
