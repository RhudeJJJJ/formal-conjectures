/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3097 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap3097 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3097 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3097_checked : acceptsGraphIso
    (source (graph core3097) (root 6) 0 5) DegreeTwoThreeSpectrum1832.graph sourceMap3097=true := by decide +kernel
theorem fusedMap3097_checked : acceptsGraphIso
    (fused (graph core3097) (root 6) 0 5) DegreeTwoThreeSpectrum1834.graph fusedMap3097=true := by decide +kernel
theorem certified3097 : Certified (graph core3097) (root 6) 0 5 :=
  of_native_maps core3097 DegreeTwoThreeSpectrum1832.graph DegreeTwoThreeSpectrum1834.graph
    sourceMap3097 fusedMap3097 sourceMap3097_checked fusedMap3097_checked
    DegreeTwoThreeFiniteComparisons.comparison3097
#print axioms sourceMap3097_checked
#print axioms fusedMap3097_checked
#print axioms certified3097
def sourceMap3097swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3097swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3097swap_checked : acceptsGraphIso
    (source (graph core3097) (root 6) 5 0) DegreeTwoThreeSpectrum1832.graph sourceMap3097swap=true := by decide +kernel
theorem fusedMap3097swap_checked : acceptsGraphIso
    (fused (graph core3097) (root 6) 5 0) DegreeTwoThreeSpectrum1834.graph fusedMap3097swap=true := by decide +kernel
theorem certified3097swap : Certified (graph core3097) (root 6) 5 0 :=
  of_native_maps core3097 DegreeTwoThreeSpectrum1832.graph DegreeTwoThreeSpectrum1834.graph
    sourceMap3097swap fusedMap3097swap sourceMap3097swap_checked fusedMap3097swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3097
#print axioms sourceMap3097swap_checked
#print axioms fusedMap3097swap_checked
#print axioms certified3097swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
