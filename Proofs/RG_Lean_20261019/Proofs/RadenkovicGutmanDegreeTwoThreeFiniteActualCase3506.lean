/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3506 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap3506 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3506 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3506_checked : acceptsGraphIso
    (source (graph core3506) (root 7) 0 6) DegreeTwoThreeSpectrum4143.graph sourceMap3506=true := by decide +kernel
theorem fusedMap3506_checked : acceptsGraphIso
    (fused (graph core3506) (root 7) 0 6) DegreeTwoThreeSpectrum3879.graph fusedMap3506=true := by decide +kernel
theorem certified3506 : Certified (graph core3506) (root 7) 0 6 :=
  of_native_maps core3506 DegreeTwoThreeSpectrum4143.graph DegreeTwoThreeSpectrum3879.graph
    sourceMap3506 fusedMap3506 sourceMap3506_checked fusedMap3506_checked
    DegreeTwoThreeFiniteComparisons.comparison3506
#print axioms sourceMap3506_checked
#print axioms fusedMap3506_checked
#print axioms certified3506
def sourceMap3506swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3506swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3506swap_checked : acceptsGraphIso
    (source (graph core3506) (root 7) 6 0) DegreeTwoThreeSpectrum4143.graph sourceMap3506swap=true := by decide +kernel
theorem fusedMap3506swap_checked : acceptsGraphIso
    (fused (graph core3506) (root 7) 6 0) DegreeTwoThreeSpectrum3879.graph fusedMap3506swap=true := by decide +kernel
theorem certified3506swap : Certified (graph core3506) (root 7) 6 0 :=
  of_native_maps core3506 DegreeTwoThreeSpectrum4143.graph DegreeTwoThreeSpectrum3879.graph
    sourceMap3506swap fusedMap3506swap sourceMap3506swap_checked fusedMap3506swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3506
#print axioms sourceMap3506swap_checked
#print axioms fusedMap3506swap_checked
#print axioms certified3506swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
