/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3115 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap3115 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3115 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3115_checked : acceptsGraphIso
    (source (graph core3115) (root 7) 0 5) DegreeTwoThreeSpectrum2759.graph sourceMap3115=true := by decide +kernel
theorem fusedMap3115_checked : acceptsGraphIso
    (fused (graph core3115) (root 7) 0 5) DegreeTwoThreeSpectrum2362.graph fusedMap3115=true := by decide +kernel
theorem certified3115 : Certified (graph core3115) (root 7) 0 5 :=
  of_native_maps core3115 DegreeTwoThreeSpectrum2759.graph DegreeTwoThreeSpectrum2362.graph
    sourceMap3115 fusedMap3115 sourceMap3115_checked fusedMap3115_checked
    DegreeTwoThreeFiniteComparisons.comparison3115
#print axioms sourceMap3115_checked
#print axioms fusedMap3115_checked
#print axioms certified3115
def sourceMap3115swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3115swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3115swap_checked : acceptsGraphIso
    (source (graph core3115) (root 7) 5 0) DegreeTwoThreeSpectrum2759.graph sourceMap3115swap=true := by decide +kernel
theorem fusedMap3115swap_checked : acceptsGraphIso
    (fused (graph core3115) (root 7) 5 0) DegreeTwoThreeSpectrum2362.graph fusedMap3115swap=true := by decide +kernel
theorem certified3115swap : Certified (graph core3115) (root 7) 5 0 :=
  of_native_maps core3115 DegreeTwoThreeSpectrum2759.graph DegreeTwoThreeSpectrum2362.graph
    sourceMap3115swap fusedMap3115swap sourceMap3115swap_checked fusedMap3115swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3115
#print axioms sourceMap3115swap_checked
#print axioms fusedMap3115swap_checked
#print axioms certified3115swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
