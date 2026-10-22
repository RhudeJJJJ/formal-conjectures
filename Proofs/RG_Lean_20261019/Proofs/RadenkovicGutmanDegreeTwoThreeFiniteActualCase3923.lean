/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3923 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3923 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,5,6,3,4,1,0,7,8,9,10] (sourceLabel 2 1 5 v)
def fusedMap3923 : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 1 5 v)
theorem sourceMap3923_checked : acceptsGraphIso
    (source (graph core3923) (root 2) 1 5) DegreeOneSmallSpectrum207.graph sourceMap3923=true := by decide +kernel
theorem fusedMap3923_checked : acceptsGraphIso
    (fused (graph core3923) (root 2) 1 5) DegreeOneSmallSpectrum164.graph fusedMap3923=true := by decide +kernel
theorem certified3923 : Certified (graph core3923) (root 2) 1 5 :=
  of_native_maps core3923 DegreeOneSmallSpectrum207.graph DegreeOneSmallSpectrum164.graph
    sourceMap3923 fusedMap3923 sourceMap3923_checked fusedMap3923_checked
    DegreeTwoThreeFiniteComparisons.comparison3923
#print axioms sourceMap3923_checked
#print axioms fusedMap3923_checked
#print axioms certified3923
def sourceMap3923swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,5,6,1,0,7,8,9,10,3,4] (sourceLabel 2 5 1 v)
def fusedMap3923swap : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 5 1 v)
theorem sourceMap3923swap_checked : acceptsGraphIso
    (source (graph core3923) (root 2) 5 1) DegreeOneSmallSpectrum207.graph sourceMap3923swap=true := by decide +kernel
theorem fusedMap3923swap_checked : acceptsGraphIso
    (fused (graph core3923) (root 2) 5 1) DegreeOneSmallSpectrum164.graph fusedMap3923swap=true := by decide +kernel
theorem certified3923swap : Certified (graph core3923) (root 2) 5 1 :=
  of_native_maps core3923 DegreeOneSmallSpectrum207.graph DegreeOneSmallSpectrum164.graph
    sourceMap3923swap fusedMap3923swap sourceMap3923swap_checked fusedMap3923swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3923
#print axioms sourceMap3923swap_checked
#print axioms fusedMap3923swap_checked
#print axioms certified3923swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
