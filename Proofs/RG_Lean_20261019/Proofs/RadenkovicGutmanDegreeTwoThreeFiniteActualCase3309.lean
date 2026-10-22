/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3309 : Family 9 := level9.get ⟨264,by decide⟩
def sourceMap3309 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3309 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3309_checked : acceptsGraphIso
    (source (graph core3309) (root 9) 0 5) DegreeTwoThreeSpectrum5711.graph sourceMap3309=true := by decide +kernel
theorem fusedMap3309_checked : acceptsGraphIso
    (fused (graph core3309) (root 9) 0 5) DegreeTwoThreeSpectrum5712.graph fusedMap3309=true := by decide +kernel
theorem certified3309 : Certified (graph core3309) (root 9) 0 5 :=
  of_native_maps core3309 DegreeTwoThreeSpectrum5711.graph DegreeTwoThreeSpectrum5712.graph
    sourceMap3309 fusedMap3309 sourceMap3309_checked fusedMap3309_checked
    DegreeTwoThreeFiniteComparisons.comparison3309
#print axioms sourceMap3309_checked
#print axioms fusedMap3309_checked
#print axioms certified3309
def sourceMap3309swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3309swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3309swap_checked : acceptsGraphIso
    (source (graph core3309) (root 9) 5 0) DegreeTwoThreeSpectrum5711.graph sourceMap3309swap=true := by decide +kernel
theorem fusedMap3309swap_checked : acceptsGraphIso
    (fused (graph core3309) (root 9) 5 0) DegreeTwoThreeSpectrum5712.graph fusedMap3309swap=true := by decide +kernel
theorem certified3309swap : Certified (graph core3309) (root 9) 5 0 :=
  of_native_maps core3309 DegreeTwoThreeSpectrum5711.graph DegreeTwoThreeSpectrum5712.graph
    sourceMap3309swap fusedMap3309swap sourceMap3309swap_checked fusedMap3309swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3309
#print axioms sourceMap3309swap_checked
#print axioms fusedMap3309swap_checked
#print axioms certified3309swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
