/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3891 : Family 8 := level8.get ⟨194,by decide⟩
def sourceMap3891 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3891 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3891_checked : acceptsGraphIso
    (source (graph core3891) (root 8) 1 4) DegreeTwoThreeSpectrum4688.graph sourceMap3891=true := by decide +kernel
theorem fusedMap3891_checked : acceptsGraphIso
    (fused (graph core3891) (root 8) 1 4) DegreeTwoThreeSpectrum4196.graph fusedMap3891=true := by decide +kernel
theorem certified3891 : Certified (graph core3891) (root 8) 1 4 :=
  of_native_maps core3891 DegreeTwoThreeSpectrum4688.graph DegreeTwoThreeSpectrum4196.graph
    sourceMap3891 fusedMap3891 sourceMap3891_checked fusedMap3891_checked
    DegreeTwoThreeFiniteComparisons.comparison3891
#print axioms sourceMap3891_checked
#print axioms fusedMap3891_checked
#print axioms certified3891
def sourceMap3891swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3891swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3891swap_checked : acceptsGraphIso
    (source (graph core3891) (root 8) 4 1) DegreeTwoThreeSpectrum4688.graph sourceMap3891swap=true := by decide +kernel
theorem fusedMap3891swap_checked : acceptsGraphIso
    (fused (graph core3891) (root 8) 4 1) DegreeTwoThreeSpectrum4196.graph fusedMap3891swap=true := by decide +kernel
theorem certified3891swap : Certified (graph core3891) (root 8) 4 1 :=
  of_native_maps core3891 DegreeTwoThreeSpectrum4688.graph DegreeTwoThreeSpectrum4196.graph
    sourceMap3891swap fusedMap3891swap sourceMap3891swap_checked fusedMap3891swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3891
#print axioms sourceMap3891swap_checked
#print axioms fusedMap3891swap_checked
#print axioms certified3891swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
