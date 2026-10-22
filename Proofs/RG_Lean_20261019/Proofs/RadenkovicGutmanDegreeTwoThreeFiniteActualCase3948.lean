/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3948 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap3948 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3948 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3948_checked : acceptsGraphIso
    (source (graph core3948) (root 6) 1 5) DegreeTwoThreeSpectrum3069.graph sourceMap3948=true := by decide +kernel
theorem fusedMap3948_checked : acceptsGraphIso
    (fused (graph core3948) (root 6) 1 5) DegreeTwoThreeSpectrum2459.graph fusedMap3948=true := by decide +kernel
theorem certified3948 : Certified (graph core3948) (root 6) 1 5 :=
  of_native_maps core3948 DegreeTwoThreeSpectrum3069.graph DegreeTwoThreeSpectrum2459.graph
    sourceMap3948 fusedMap3948 sourceMap3948_checked fusedMap3948_checked
    DegreeTwoThreeFiniteComparisons.comparison3948
#print axioms sourceMap3948_checked
#print axioms fusedMap3948_checked
#print axioms certified3948
def sourceMap3948swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,9,10] (sourceLabel 6 5 1 v)
def fusedMap3948swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3948swap_checked : acceptsGraphIso
    (source (graph core3948) (root 6) 5 1) DegreeTwoThreeSpectrum3069.graph sourceMap3948swap=true := by decide +kernel
theorem fusedMap3948swap_checked : acceptsGraphIso
    (fused (graph core3948) (root 6) 5 1) DegreeTwoThreeSpectrum2459.graph fusedMap3948swap=true := by decide +kernel
theorem certified3948swap : Certified (graph core3948) (root 6) 5 1 :=
  of_native_maps core3948 DegreeTwoThreeSpectrum3069.graph DegreeTwoThreeSpectrum2459.graph
    sourceMap3948swap fusedMap3948swap sourceMap3948swap_checked fusedMap3948swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3948
#print axioms sourceMap3948swap_checked
#print axioms fusedMap3948swap_checked
#print axioms certified3948swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
