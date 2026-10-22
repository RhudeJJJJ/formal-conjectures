/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3764 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3764 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,6,4,5,0,7,8,9,10] (sourceLabel 3 1 4 v)
def fusedMap3764 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 1 4 v)
theorem sourceMap3764_checked : acceptsGraphIso
    (source (graph core3764) (root 3) 1 4) DegreeOneSmallSpectrum198.graph sourceMap3764=true := by decide +kernel
theorem fusedMap3764_checked : acceptsGraphIso
    (fused (graph core3764) (root 3) 1 4) DegreeOneSmallSpectrum165.graph fusedMap3764=true := by decide +kernel
theorem certified3764 : Certified (graph core3764) (root 3) 1 4 :=
  of_native_maps core3764 DegreeOneSmallSpectrum198.graph DegreeOneSmallSpectrum165.graph
    sourceMap3764 fusedMap3764 sourceMap3764_checked fusedMap3764_checked
    DegreeTwoThreeFiniteComparisons.comparison3764
#print axioms sourceMap3764_checked
#print axioms fusedMap3764_checked
#print axioms certified3764
def sourceMap3764swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,2,3,6,0,7,8,9,10,4,5] (sourceLabel 3 4 1 v)
def fusedMap3764swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 4 1 v)
theorem sourceMap3764swap_checked : acceptsGraphIso
    (source (graph core3764) (root 3) 4 1) DegreeOneSmallSpectrum198.graph sourceMap3764swap=true := by decide +kernel
theorem fusedMap3764swap_checked : acceptsGraphIso
    (fused (graph core3764) (root 3) 4 1) DegreeOneSmallSpectrum165.graph fusedMap3764swap=true := by decide +kernel
theorem certified3764swap : Certified (graph core3764) (root 3) 4 1 :=
  of_native_maps core3764 DegreeOneSmallSpectrum198.graph DegreeOneSmallSpectrum165.graph
    sourceMap3764swap fusedMap3764swap sourceMap3764swap_checked fusedMap3764swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3764
#print axioms sourceMap3764swap_checked
#print axioms fusedMap3764swap_checked
#print axioms certified3764swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
