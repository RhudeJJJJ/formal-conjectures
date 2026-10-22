/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3480 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3480 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (sourceLabel 5 0 6 v)
def fusedMap3480 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 0 6 v)
theorem sourceMap3480_checked : acceptsGraphIso
    (source (graph core3480) (root 5) 0 6) DegreeTwoThreeSpectrum1730.graph sourceMap3480=true := by decide +kernel
theorem fusedMap3480_checked : acceptsGraphIso
    (fused (graph core3480) (root 5) 0 6) DegreeTwoThreeSpectrum1734.graph fusedMap3480=true := by decide +kernel
theorem certified3480 : Certified (graph core3480) (root 5) 0 6 :=
  of_native_maps core3480 DegreeTwoThreeSpectrum1730.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap3480 fusedMap3480 sourceMap3480_checked fusedMap3480_checked
    DegreeTwoThreeFiniteComparisons.comparison3480
#print axioms sourceMap3480_checked
#print axioms fusedMap3480_checked
#print axioms certified3480
def sourceMap3480swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,13,7] (sourceLabel 5 6 0 v)
def fusedMap3480swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 6 0 v)
theorem sourceMap3480swap_checked : acceptsGraphIso
    (source (graph core3480) (root 5) 6 0) DegreeTwoThreeSpectrum1730.graph sourceMap3480swap=true := by decide +kernel
theorem fusedMap3480swap_checked : acceptsGraphIso
    (fused (graph core3480) (root 5) 6 0) DegreeTwoThreeSpectrum1734.graph fusedMap3480swap=true := by decide +kernel
theorem certified3480swap : Certified (graph core3480) (root 5) 6 0 :=
  of_native_maps core3480 DegreeTwoThreeSpectrum1730.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap3480swap fusedMap3480swap sourceMap3480swap_checked fusedMap3480swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3480
#print axioms sourceMap3480swap_checked
#print axioms fusedMap3480swap_checked
#print axioms certified3480swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
