/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3136 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap3136 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3136 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3136_checked : acceptsGraphIso
    (source (graph core3136) (root 7) 0 5) DegreeTwoThreeSpectrum2827.graph sourceMap3136=true := by decide +kernel
theorem fusedMap3136_checked : acceptsGraphIso
    (fused (graph core3136) (root 7) 0 5) DegreeTwoThreeSpectrum2829.graph fusedMap3136=true := by decide +kernel
theorem certified3136 : Certified (graph core3136) (root 7) 0 5 :=
  of_native_maps core3136 DegreeTwoThreeSpectrum2827.graph DegreeTwoThreeSpectrum2829.graph
    sourceMap3136 fusedMap3136 sourceMap3136_checked fusedMap3136_checked
    DegreeTwoThreeFiniteComparisons.comparison3136
#print axioms sourceMap3136_checked
#print axioms fusedMap3136_checked
#print axioms certified3136
def sourceMap3136swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3136swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3136swap_checked : acceptsGraphIso
    (source (graph core3136) (root 7) 5 0) DegreeTwoThreeSpectrum2827.graph sourceMap3136swap=true := by decide +kernel
theorem fusedMap3136swap_checked : acceptsGraphIso
    (fused (graph core3136) (root 7) 5 0) DegreeTwoThreeSpectrum2829.graph fusedMap3136swap=true := by decide +kernel
theorem certified3136swap : Certified (graph core3136) (root 7) 5 0 :=
  of_native_maps core3136 DegreeTwoThreeSpectrum2827.graph DegreeTwoThreeSpectrum2829.graph
    sourceMap3136swap fusedMap3136swap sourceMap3136swap_checked fusedMap3136swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3136
#print axioms sourceMap3136swap_checked
#print axioms fusedMap3136swap_checked
#print axioms certified3136swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
