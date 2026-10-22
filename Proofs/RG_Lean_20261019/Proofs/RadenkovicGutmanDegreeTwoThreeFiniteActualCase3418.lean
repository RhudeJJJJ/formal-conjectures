/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3418 : Family 9 := level9.get ⟨531,by decide⟩
def sourceMap3418 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3418 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3418_checked : acceptsGraphIso
    (source (graph core3418) (root 9) 0 5) DegreeTwoThreeSpectrum7012.graph sourceMap3418=true := by decide +kernel
theorem fusedMap3418_checked : acceptsGraphIso
    (fused (graph core3418) (root 9) 0 5) DegreeTwoThreeSpectrum5827.graph fusedMap3418=true := by decide +kernel
theorem certified3418 : Certified (graph core3418) (root 9) 0 5 :=
  of_native_maps core3418 DegreeTwoThreeSpectrum7012.graph DegreeTwoThreeSpectrum5827.graph
    sourceMap3418 fusedMap3418 sourceMap3418_checked fusedMap3418_checked
    DegreeTwoThreeFiniteComparisons.comparison3418
#print axioms sourceMap3418_checked
#print axioms fusedMap3418_checked
#print axioms certified3418
def sourceMap3418swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3418swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3418swap_checked : acceptsGraphIso
    (source (graph core3418) (root 9) 5 0) DegreeTwoThreeSpectrum7012.graph sourceMap3418swap=true := by decide +kernel
theorem fusedMap3418swap_checked : acceptsGraphIso
    (fused (graph core3418) (root 9) 5 0) DegreeTwoThreeSpectrum5827.graph fusedMap3418swap=true := by decide +kernel
theorem certified3418swap : Certified (graph core3418) (root 9) 5 0 :=
  of_native_maps core3418 DegreeTwoThreeSpectrum7012.graph DegreeTwoThreeSpectrum5827.graph
    sourceMap3418swap fusedMap3418swap sourceMap3418swap_checked fusedMap3418swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3418
#print axioms sourceMap3418swap_checked
#print axioms fusedMap3418swap_checked
#print axioms certified3418swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
