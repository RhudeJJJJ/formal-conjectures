/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3757 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3757 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,5,3,4,6,7,8] (sourceLabel 3 1 2 v)
def fusedMap3757 : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 1 2 v)
theorem sourceMap3757_checked : acceptsGraphIso
    (source (graph core3757) (root 3) 1 2) DegreeOneSmallSpectrum053.graph sourceMap3757=true := by decide +kernel
theorem fusedMap3757_checked : acceptsGraphIso
    (fused (graph core3757) (root 3) 1 2) DegreeOneSmallSpectrum035.graph fusedMap3757=true := by decide +kernel
theorem certified3757 : Certified (graph core3757) (root 3) 1 2 :=
  of_native_maps core3757 DegreeOneSmallSpectrum053.graph DegreeOneSmallSpectrum035.graph
    sourceMap3757 fusedMap3757 sourceMap3757_checked fusedMap3757_checked
    DegreeTwoThreeFiniteComparisons.comparison3757
#print axioms sourceMap3757_checked
#print axioms fusedMap3757_checked
#print axioms certified3757
def sourceMap3757swap : (Vertices 3 ⊕ Fin 3 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,5,6,7,8,3,4] (sourceLabel 3 2 1 v)
def fusedMap3757swap : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 2 1 v)
theorem sourceMap3757swap_checked : acceptsGraphIso
    (source (graph core3757) (root 3) 2 1) DegreeOneSmallSpectrum053.graph sourceMap3757swap=true := by decide +kernel
theorem fusedMap3757swap_checked : acceptsGraphIso
    (fused (graph core3757) (root 3) 2 1) DegreeOneSmallSpectrum035.graph fusedMap3757swap=true := by decide +kernel
theorem certified3757swap : Certified (graph core3757) (root 3) 2 1 :=
  of_native_maps core3757 DegreeOneSmallSpectrum053.graph DegreeOneSmallSpectrum035.graph
    sourceMap3757swap fusedMap3757swap sourceMap3757swap_checked fusedMap3757swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3757
#print axioms sourceMap3757swap_checked
#print axioms fusedMap3757swap_checked
#print axioms certified3757swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
