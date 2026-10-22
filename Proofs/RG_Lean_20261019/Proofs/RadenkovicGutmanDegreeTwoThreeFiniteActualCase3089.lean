/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3089 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap3089 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3089 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3089_checked : acceptsGraphIso
    (source (graph core3089) (root 6) 0 5) DegreeTwoThreeSpectrum1847.graph sourceMap3089=true := by decide +kernel
theorem fusedMap3089_checked : acceptsGraphIso
    (fused (graph core3089) (root 6) 0 5) DegreeTwoThreeSpectrum1719.graph fusedMap3089=true := by decide +kernel
theorem certified3089 : Certified (graph core3089) (root 6) 0 5 :=
  of_native_maps core3089 DegreeTwoThreeSpectrum1847.graph DegreeTwoThreeSpectrum1719.graph
    sourceMap3089 fusedMap3089 sourceMap3089_checked fusedMap3089_checked
    DegreeTwoThreeFiniteComparisons.comparison3089
#print axioms sourceMap3089_checked
#print axioms fusedMap3089_checked
#print axioms certified3089
def sourceMap3089swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3089swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3089swap_checked : acceptsGraphIso
    (source (graph core3089) (root 6) 5 0) DegreeTwoThreeSpectrum1847.graph sourceMap3089swap=true := by decide +kernel
theorem fusedMap3089swap_checked : acceptsGraphIso
    (fused (graph core3089) (root 6) 5 0) DegreeTwoThreeSpectrum1719.graph fusedMap3089swap=true := by decide +kernel
theorem certified3089swap : Certified (graph core3089) (root 6) 5 0 :=
  of_native_maps core3089 DegreeTwoThreeSpectrum1847.graph DegreeTwoThreeSpectrum1719.graph
    sourceMap3089swap fusedMap3089swap sourceMap3089swap_checked fusedMap3089swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3089
#print axioms sourceMap3089swap_checked
#print axioms fusedMap3089swap_checked
#print axioms certified3089swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
