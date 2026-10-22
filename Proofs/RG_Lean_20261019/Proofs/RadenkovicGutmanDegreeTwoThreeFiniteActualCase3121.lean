/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3121 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap3121 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3121 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3121_checked : acceptsGraphIso
    (source (graph core3121) (root 7) 0 5) DegreeTwoThreeSpectrum2967.graph sourceMap3121=true := by decide +kernel
theorem fusedMap3121_checked : acceptsGraphIso
    (fused (graph core3121) (root 7) 0 5) DegreeTwoThreeSpectrum2409.graph fusedMap3121=true := by decide +kernel
theorem certified3121 : Certified (graph core3121) (root 7) 0 5 :=
  of_native_maps core3121 DegreeTwoThreeSpectrum2967.graph DegreeTwoThreeSpectrum2409.graph
    sourceMap3121 fusedMap3121 sourceMap3121_checked fusedMap3121_checked
    DegreeTwoThreeFiniteComparisons.comparison3121
#print axioms sourceMap3121_checked
#print axioms fusedMap3121_checked
#print axioms certified3121
def sourceMap3121swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3121swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3121swap_checked : acceptsGraphIso
    (source (graph core3121) (root 7) 5 0) DegreeTwoThreeSpectrum2967.graph sourceMap3121swap=true := by decide +kernel
theorem fusedMap3121swap_checked : acceptsGraphIso
    (fused (graph core3121) (root 7) 5 0) DegreeTwoThreeSpectrum2409.graph fusedMap3121swap=true := by decide +kernel
theorem certified3121swap : Certified (graph core3121) (root 7) 5 0 :=
  of_native_maps core3121 DegreeTwoThreeSpectrum2967.graph DegreeTwoThreeSpectrum2409.graph
    sourceMap3121swap fusedMap3121swap sourceMap3121swap_checked fusedMap3121swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3121
#print axioms sourceMap3121swap_checked
#print axioms fusedMap3121swap_checked
#print axioms certified3121swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
