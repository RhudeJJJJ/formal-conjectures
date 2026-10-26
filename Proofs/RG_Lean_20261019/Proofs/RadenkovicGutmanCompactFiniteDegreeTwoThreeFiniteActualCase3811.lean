/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3811 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap3811 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3811 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3811_checked : acceptsGraphIso
    (source (graph core3811) (root 7) 1 4) DegreeTwoThreeSpectrum3126.graph sourceMap3811=true := by decide +kernel
theorem fusedMap3811_checked : acceptsGraphIso
    (fused (graph core3811) (root 7) 1 4) DegreeTwoThreeSpectrum2477.graph fusedMap3811=true := by decide +kernel
theorem certified3811 : Certified (graph core3811) (root 7) 1 4 :=
  of_native_maps core3811 DegreeTwoThreeSpectrum3126.graph DegreeTwoThreeSpectrum2477.graph
    sourceMap3811 fusedMap3811 sourceMap3811_checked fusedMap3811_checked
    DegreeTwoThreeFiniteComparisons.comparison3811
#print axioms sourceMap3811_checked
#print axioms fusedMap3811_checked
#print axioms certified3811
def sourceMap3811swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3811swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3811swap_checked : acceptsGraphIso
    (source (graph core3811) (root 7) 4 1) DegreeTwoThreeSpectrum3126.graph sourceMap3811swap=true := by decide +kernel
theorem fusedMap3811swap_checked : acceptsGraphIso
    (fused (graph core3811) (root 7) 4 1) DegreeTwoThreeSpectrum2477.graph fusedMap3811swap=true := by decide +kernel
theorem certified3811swap : Certified (graph core3811) (root 7) 4 1 :=
  of_native_maps core3811 DegreeTwoThreeSpectrum3126.graph DegreeTwoThreeSpectrum2477.graph
    sourceMap3811swap fusedMap3811swap sourceMap3811swap_checked fusedMap3811swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3811
#print axioms sourceMap3811swap_checked
#print axioms fusedMap3811swap_checked
#print axioms certified3811swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
