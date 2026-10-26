/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3646 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap3646 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3646 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3646_checked : acceptsGraphIso
    (source (graph core3646) (root 6) 0 7) DegreeTwoThreeSpectrum3884.graph sourceMap3646=true := by decide +kernel
theorem fusedMap3646_checked : acceptsGraphIso
    (fused (graph core3646) (root 6) 0 7) DegreeTwoThreeSpectrum3887.graph fusedMap3646=true := by decide +kernel
theorem certified3646 : Certified (graph core3646) (root 6) 0 7 :=
  of_native_maps core3646 DegreeTwoThreeSpectrum3884.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap3646 fusedMap3646 sourceMap3646_checked fusedMap3646_checked
    DegreeTwoThreeFiniteComparisons.comparison3646
#print axioms sourceMap3646_checked
#print axioms fusedMap3646_checked
#print axioms certified3646
def sourceMap3646swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,8] (sourceLabel 6 7 0 v)
def fusedMap3646swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3646swap_checked : acceptsGraphIso
    (source (graph core3646) (root 6) 7 0) DegreeTwoThreeSpectrum3884.graph sourceMap3646swap=true := by decide +kernel
theorem fusedMap3646swap_checked : acceptsGraphIso
    (fused (graph core3646) (root 6) 7 0) DegreeTwoThreeSpectrum3887.graph fusedMap3646swap=true := by decide +kernel
theorem certified3646swap : Certified (graph core3646) (root 6) 7 0 :=
  of_native_maps core3646 DegreeTwoThreeSpectrum3884.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap3646swap fusedMap3646swap sourceMap3646swap_checked fusedMap3646swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3646
#print axioms sourceMap3646swap_checked
#print axioms fusedMap3646swap_checked
#print axioms certified3646swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
