/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3983 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap3983 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3983 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3983_checked : acceptsGraphIso
    (source (graph core3983) (root 7) 1 5) DegreeTwoThreeSpectrum4565.graph sourceMap3983=true := by decide +kernel
theorem fusedMap3983_checked : acceptsGraphIso
    (fused (graph core3983) (root 7) 1 5) DegreeTwoThreeSpectrum4063.graph fusedMap3983=true := by decide +kernel
theorem certified3983 : Certified (graph core3983) (root 7) 1 5 :=
  of_native_maps core3983 DegreeTwoThreeSpectrum4565.graph DegreeTwoThreeSpectrum4063.graph
    sourceMap3983 fusedMap3983 sourceMap3983_checked fusedMap3983_checked
    DegreeTwoThreeFiniteComparisons.comparison3983
#print axioms sourceMap3983_checked
#print axioms fusedMap3983_checked
#print axioms certified3983
def sourceMap3983swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3983swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3983swap_checked : acceptsGraphIso
    (source (graph core3983) (root 7) 5 1) DegreeTwoThreeSpectrum4565.graph sourceMap3983swap=true := by decide +kernel
theorem fusedMap3983swap_checked : acceptsGraphIso
    (fused (graph core3983) (root 7) 5 1) DegreeTwoThreeSpectrum4063.graph fusedMap3983swap=true := by decide +kernel
theorem certified3983swap : Certified (graph core3983) (root 7) 5 1 :=
  of_native_maps core3983 DegreeTwoThreeSpectrum4565.graph DegreeTwoThreeSpectrum4063.graph
    sourceMap3983swap fusedMap3983swap sourceMap3983swap_checked fusedMap3983swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3983
#print axioms sourceMap3983swap_checked
#print axioms fusedMap3983swap_checked
#print axioms certified3983swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
