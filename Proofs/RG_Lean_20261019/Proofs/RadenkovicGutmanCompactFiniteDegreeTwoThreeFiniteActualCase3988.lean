/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3988 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3988 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,7,5,6,1,0,8,9,10,11,12] (sourceLabel 3 1 6 v)
def fusedMap3988 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 1 6 v)
theorem sourceMap3988_checked : acceptsGraphIso
    (source (graph core3988) (root 3) 1 6) DegreeOneSmallSpectrum909.graph sourceMap3988=true := by decide +kernel
theorem fusedMap3988_checked : acceptsGraphIso
    (fused (graph core3988) (root 3) 1 6) DegreeOneSmallSpectrum857.graph fusedMap3988=true := by decide +kernel
theorem certified3988 : Certified (graph core3988) (root 3) 1 6 :=
  of_native_maps core3988 DegreeOneSmallSpectrum909.graph DegreeOneSmallSpectrum857.graph
    sourceMap3988 fusedMap3988 sourceMap3988_checked fusedMap3988_checked
    DegreeTwoThreeFiniteComparisons.comparison3988
#print axioms sourceMap3988_checked
#print axioms fusedMap3988_checked
#print axioms certified3988
def sourceMap3988swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,3,4,7,1,0,8,9,10,11,12,5,6] (sourceLabel 3 6 1 v)
def fusedMap3988swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 6 1 v)
theorem sourceMap3988swap_checked : acceptsGraphIso
    (source (graph core3988) (root 3) 6 1) DegreeOneSmallSpectrum909.graph sourceMap3988swap=true := by decide +kernel
theorem fusedMap3988swap_checked : acceptsGraphIso
    (fused (graph core3988) (root 3) 6 1) DegreeOneSmallSpectrum857.graph fusedMap3988swap=true := by decide +kernel
theorem certified3988swap : Certified (graph core3988) (root 3) 6 1 :=
  of_native_maps core3988 DegreeOneSmallSpectrum909.graph DegreeOneSmallSpectrum857.graph
    sourceMap3988swap fusedMap3988swap sourceMap3988swap_checked fusedMap3988swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3988
#print axioms sourceMap3988swap_checked
#print axioms fusedMap3988swap_checked
#print axioms certified3988swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
