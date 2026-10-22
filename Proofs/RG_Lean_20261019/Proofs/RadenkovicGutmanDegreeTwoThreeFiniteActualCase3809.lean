/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3809 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap3809 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3809 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3809_checked : acceptsGraphIso
    (source (graph core3809) (root 7) 1 4) DegreeTwoThreeSpectrum3045.graph sourceMap3809=true := by decide +kernel
theorem fusedMap3809_checked : acceptsGraphIso
    (fused (graph core3809) (root 7) 1 4) DegreeTwoThreeSpectrum2448.graph fusedMap3809=true := by decide +kernel
theorem certified3809 : Certified (graph core3809) (root 7) 1 4 :=
  of_native_maps core3809 DegreeTwoThreeSpectrum3045.graph DegreeTwoThreeSpectrum2448.graph
    sourceMap3809 fusedMap3809 sourceMap3809_checked fusedMap3809_checked
    DegreeTwoThreeFiniteComparisons.comparison3809
#print axioms sourceMap3809_checked
#print axioms fusedMap3809_checked
#print axioms certified3809
def sourceMap3809swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3809swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3809swap_checked : acceptsGraphIso
    (source (graph core3809) (root 7) 4 1) DegreeTwoThreeSpectrum3045.graph sourceMap3809swap=true := by decide +kernel
theorem fusedMap3809swap_checked : acceptsGraphIso
    (fused (graph core3809) (root 7) 4 1) DegreeTwoThreeSpectrum2448.graph fusedMap3809swap=true := by decide +kernel
theorem certified3809swap : Certified (graph core3809) (root 7) 4 1 :=
  of_native_maps core3809 DegreeTwoThreeSpectrum3045.graph DegreeTwoThreeSpectrum2448.graph
    sourceMap3809swap fusedMap3809swap sourceMap3809swap_checked fusedMap3809swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3809
#print axioms sourceMap3809swap_checked
#print axioms fusedMap3809swap_checked
#print axioms certified3809swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
