/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3924 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3924 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,7,5,6,1,0,8,9,10,11] (sourceLabel 3 1 5 v)
def fusedMap3924 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 1 5 v)
theorem sourceMap3924_checked : acceptsGraphIso
    (source (graph core3924) (root 3) 1 5) DegreeOneSmallSpectrum505.graph sourceMap3924=true := by decide +kernel
theorem fusedMap3924_checked : acceptsGraphIso
    (fused (graph core3924) (root 3) 1 5) DegreeOneSmallSpectrum386.graph fusedMap3924=true := by decide +kernel
theorem certified3924 : Certified (graph core3924) (root 3) 1 5 :=
  of_native_maps core3924 DegreeOneSmallSpectrum505.graph DegreeOneSmallSpectrum386.graph
    sourceMap3924 fusedMap3924 sourceMap3924_checked fusedMap3924_checked
    DegreeTwoThreeFiniteComparisons.comparison3924
#print axioms sourceMap3924_checked
#print axioms fusedMap3924_checked
#print axioms certified3924
def sourceMap3924swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,3,4,7,1,0,8,9,10,11,5,6] (sourceLabel 3 5 1 v)
def fusedMap3924swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 5 1 v)
theorem sourceMap3924swap_checked : acceptsGraphIso
    (source (graph core3924) (root 3) 5 1) DegreeOneSmallSpectrum505.graph sourceMap3924swap=true := by decide +kernel
theorem fusedMap3924swap_checked : acceptsGraphIso
    (fused (graph core3924) (root 3) 5 1) DegreeOneSmallSpectrum386.graph fusedMap3924swap=true := by decide +kernel
theorem certified3924swap : Certified (graph core3924) (root 3) 5 1 :=
  of_native_maps core3924 DegreeOneSmallSpectrum505.graph DegreeOneSmallSpectrum386.graph
    sourceMap3924swap fusedMap3924swap sourceMap3924swap_checked fusedMap3924swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3924
#print axioms sourceMap3924swap_checked
#print axioms fusedMap3924swap_checked
#print axioms certified3924swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
