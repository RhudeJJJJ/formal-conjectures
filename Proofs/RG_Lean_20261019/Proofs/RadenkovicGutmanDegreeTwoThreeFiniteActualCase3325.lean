/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3325 : Family 9 := level9.get ⟨304,by decide⟩
def sourceMap3325 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3325 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3325_checked : acceptsGraphIso
    (source (graph core3325) (root 9) 0 5) DegreeTwoThreeSpectrum5888.graph sourceMap3325=true := by decide +kernel
theorem fusedMap3325_checked : acceptsGraphIso
    (fused (graph core3325) (root 9) 0 5) DegreeTwoThreeSpectrum5889.graph fusedMap3325=true := by decide +kernel
theorem certified3325 : Certified (graph core3325) (root 9) 0 5 :=
  of_native_maps core3325 DegreeTwoThreeSpectrum5888.graph DegreeTwoThreeSpectrum5889.graph
    sourceMap3325 fusedMap3325 sourceMap3325_checked fusedMap3325_checked
    DegreeTwoThreeFiniteComparisons.comparison3325
#print axioms sourceMap3325_checked
#print axioms fusedMap3325_checked
#print axioms certified3325
def sourceMap3325swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3325swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3325swap_checked : acceptsGraphIso
    (source (graph core3325) (root 9) 5 0) DegreeTwoThreeSpectrum5888.graph sourceMap3325swap=true := by decide +kernel
theorem fusedMap3325swap_checked : acceptsGraphIso
    (fused (graph core3325) (root 9) 5 0) DegreeTwoThreeSpectrum5889.graph fusedMap3325swap=true := by decide +kernel
theorem certified3325swap : Certified (graph core3325) (root 9) 5 0 :=
  of_native_maps core3325 DegreeTwoThreeSpectrum5888.graph DegreeTwoThreeSpectrum5889.graph
    sourceMap3325swap fusedMap3325swap sourceMap3325swap_checked fusedMap3325swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3325
#print axioms sourceMap3325swap_checked
#print axioms fusedMap3325swap_checked
#print axioms certified3325swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
