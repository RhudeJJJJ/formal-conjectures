/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3490 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap3490 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3490 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3490_checked : acceptsGraphIso
    (source (graph core3490) (root 6) 0 6) DegreeTwoThreeSpectrum2410.graph sourceMap3490=true := by decide +kernel
theorem fusedMap3490_checked : acceptsGraphIso
    (fused (graph core3490) (root 6) 0 6) DegreeTwoThreeSpectrum2414.graph fusedMap3490=true := by decide +kernel
theorem certified3490 : Certified (graph core3490) (root 6) 0 6 :=
  of_native_maps core3490 DegreeTwoThreeSpectrum2410.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap3490 fusedMap3490 sourceMap3490_checked fusedMap3490_checked
    DegreeTwoThreeFiniteComparisons.comparison3490
#print axioms sourceMap3490_checked
#print axioms fusedMap3490_checked
#print axioms certified3490
def sourceMap3490swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,14,8] (sourceLabel 6 6 0 v)
def fusedMap3490swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3490swap_checked : acceptsGraphIso
    (source (graph core3490) (root 6) 6 0) DegreeTwoThreeSpectrum2410.graph sourceMap3490swap=true := by decide +kernel
theorem fusedMap3490swap_checked : acceptsGraphIso
    (fused (graph core3490) (root 6) 6 0) DegreeTwoThreeSpectrum2414.graph fusedMap3490swap=true := by decide +kernel
theorem certified3490swap : Certified (graph core3490) (root 6) 6 0 :=
  of_native_maps core3490 DegreeTwoThreeSpectrum2410.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap3490swap fusedMap3490swap sourceMap3490swap_checked fusedMap3490swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3490
#print axioms sourceMap3490swap_checked
#print axioms fusedMap3490swap_checked
#print axioms certified3490swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
