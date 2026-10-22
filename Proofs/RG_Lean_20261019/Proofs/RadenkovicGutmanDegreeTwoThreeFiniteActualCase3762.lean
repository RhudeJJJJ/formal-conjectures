/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3762 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3762 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,6,4,5,0,7,8,9] (sourceLabel 3 1 3 v)
def fusedMap3762 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 1 3 v)
theorem sourceMap3762_checked : acceptsGraphIso
    (source (graph core3762) (root 3) 1 3) DegreeOneSmallSpectrum133.graph sourceMap3762=true := by decide +kernel
theorem fusedMap3762_checked : acceptsGraphIso
    (fused (graph core3762) (root 3) 1 3) DegreeOneSmallSpectrum086.graph fusedMap3762=true := by decide +kernel
theorem certified3762 : Certified (graph core3762) (root 3) 1 3 :=
  of_native_maps core3762 DegreeOneSmallSpectrum133.graph DegreeOneSmallSpectrum086.graph
    sourceMap3762 fusedMap3762 sourceMap3762_checked fusedMap3762_checked
    DegreeTwoThreeFiniteComparisons.comparison3762
#print axioms sourceMap3762_checked
#print axioms fusedMap3762_checked
#print axioms certified3762
def sourceMap3762swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,2,3,6,0,7,8,9,4,5] (sourceLabel 3 3 1 v)
def fusedMap3762swap : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 3 1 v)
theorem sourceMap3762swap_checked : acceptsGraphIso
    (source (graph core3762) (root 3) 3 1) DegreeOneSmallSpectrum133.graph sourceMap3762swap=true := by decide +kernel
theorem fusedMap3762swap_checked : acceptsGraphIso
    (fused (graph core3762) (root 3) 3 1) DegreeOneSmallSpectrum086.graph fusedMap3762swap=true := by decide +kernel
theorem certified3762swap : Certified (graph core3762) (root 3) 3 1 :=
  of_native_maps core3762 DegreeOneSmallSpectrum133.graph DegreeOneSmallSpectrum086.graph
    sourceMap3762swap fusedMap3762swap sourceMap3762swap_checked fusedMap3762swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3762
#print axioms sourceMap3762swap_checked
#print axioms fusedMap3762swap_checked
#print axioms certified3762swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
