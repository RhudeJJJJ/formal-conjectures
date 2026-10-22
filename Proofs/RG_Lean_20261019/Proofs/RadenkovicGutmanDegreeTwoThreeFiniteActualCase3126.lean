/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3126 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap3126 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3126 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3126_checked : acceptsGraphIso
    (source (graph core3126) (root 7) 0 5) DegreeTwoThreeSpectrum2523.graph sourceMap3126=true := by decide +kernel
theorem fusedMap3126_checked : acceptsGraphIso
    (fused (graph core3126) (root 7) 0 5) DegreeTwoThreeSpectrum2525.graph fusedMap3126=true := by decide +kernel
theorem certified3126 : Certified (graph core3126) (root 7) 0 5 :=
  of_native_maps core3126 DegreeTwoThreeSpectrum2523.graph DegreeTwoThreeSpectrum2525.graph
    sourceMap3126 fusedMap3126 sourceMap3126_checked fusedMap3126_checked
    DegreeTwoThreeFiniteComparisons.comparison3126
#print axioms sourceMap3126_checked
#print axioms fusedMap3126_checked
#print axioms certified3126
def sourceMap3126swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3126swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3126swap_checked : acceptsGraphIso
    (source (graph core3126) (root 7) 5 0) DegreeTwoThreeSpectrum2523.graph sourceMap3126swap=true := by decide +kernel
theorem fusedMap3126swap_checked : acceptsGraphIso
    (fused (graph core3126) (root 7) 5 0) DegreeTwoThreeSpectrum2525.graph fusedMap3126swap=true := by decide +kernel
theorem certified3126swap : Certified (graph core3126) (root 7) 5 0 :=
  of_native_maps core3126 DegreeTwoThreeSpectrum2523.graph DegreeTwoThreeSpectrum2525.graph
    sourceMap3126swap fusedMap3126swap sourceMap3126swap_checked fusedMap3126swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3126
#print axioms sourceMap3126swap_checked
#print axioms fusedMap3126swap_checked
#print axioms certified3126swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
