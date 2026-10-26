/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3931 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3931 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 5 1 5 v)
def fusedMap3931 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 1 5 v)
theorem sourceMap3931_checked : acceptsGraphIso
    (source (graph core3931) (root 5) 1 5) DegreeTwoThreeSpectrum1866.graph sourceMap3931=true := by decide +kernel
theorem fusedMap3931_checked : acceptsGraphIso
    (fused (graph core3931) (root 5) 1 5) DegreeTwoThreeSpectrum1723.graph fusedMap3931=true := by decide +kernel
theorem certified3931 : Certified (graph core3931) (root 5) 1 5 :=
  of_native_maps core3931 DegreeTwoThreeSpectrum1866.graph DegreeTwoThreeSpectrum1723.graph
    sourceMap3931 fusedMap3931 sourceMap3931_checked fusedMap3931_checked
    DegreeTwoThreeFiniteComparisons.comparison3931
#print axioms sourceMap3931_checked
#print axioms fusedMap3931_checked
#print axioms certified3931
def sourceMap3931swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,13,7,8] (sourceLabel 5 5 1 v)
def fusedMap3931swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 5 1 v)
theorem sourceMap3931swap_checked : acceptsGraphIso
    (source (graph core3931) (root 5) 5 1) DegreeTwoThreeSpectrum1866.graph sourceMap3931swap=true := by decide +kernel
theorem fusedMap3931swap_checked : acceptsGraphIso
    (fused (graph core3931) (root 5) 5 1) DegreeTwoThreeSpectrum1723.graph fusedMap3931swap=true := by decide +kernel
theorem certified3931swap : Certified (graph core3931) (root 5) 5 1 :=
  of_native_maps core3931 DegreeTwoThreeSpectrum1866.graph DegreeTwoThreeSpectrum1723.graph
    sourceMap3931swap fusedMap3931swap sourceMap3931swap_checked fusedMap3931swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3931
#print axioms sourceMap3931swap_checked
#print axioms fusedMap3931swap_checked
#print axioms certified3931swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
