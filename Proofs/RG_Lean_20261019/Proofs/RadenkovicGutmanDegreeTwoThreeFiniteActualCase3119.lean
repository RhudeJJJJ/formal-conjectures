/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3119 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap3119 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3119 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3119_checked : acceptsGraphIso
    (source (graph core3119) (root 7) 0 5) DegreeTwoThreeSpectrum2919.graph sourceMap3119=true := by decide +kernel
theorem fusedMap3119_checked : acceptsGraphIso
    (fused (graph core3119) (root 7) 0 5) DegreeTwoThreeSpectrum2394.graph fusedMap3119=true := by decide +kernel
theorem certified3119 : Certified (graph core3119) (root 7) 0 5 :=
  of_native_maps core3119 DegreeTwoThreeSpectrum2919.graph DegreeTwoThreeSpectrum2394.graph
    sourceMap3119 fusedMap3119 sourceMap3119_checked fusedMap3119_checked
    DegreeTwoThreeFiniteComparisons.comparison3119
#print axioms sourceMap3119_checked
#print axioms fusedMap3119_checked
#print axioms certified3119
def sourceMap3119swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3119swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3119swap_checked : acceptsGraphIso
    (source (graph core3119) (root 7) 5 0) DegreeTwoThreeSpectrum2919.graph sourceMap3119swap=true := by decide +kernel
theorem fusedMap3119swap_checked : acceptsGraphIso
    (fused (graph core3119) (root 7) 5 0) DegreeTwoThreeSpectrum2394.graph fusedMap3119swap=true := by decide +kernel
theorem certified3119swap : Certified (graph core3119) (root 7) 5 0 :=
  of_native_maps core3119 DegreeTwoThreeSpectrum2919.graph DegreeTwoThreeSpectrum2394.graph
    sourceMap3119swap fusedMap3119swap sourceMap3119swap_checked fusedMap3119swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3119
#print axioms sourceMap3119swap_checked
#print axioms fusedMap3119swap_checked
#print axioms certified3119swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
