/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5461 : Family 5 := level5.get ⟨17,by decide⟩
def sourceMap5461 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 0 2 v)
def fusedMap5461 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap5461_checked : acceptsGraphIso
    (source (graph core5461) (root 5) 0 2) SmallGeFourSpectrum019.graph sourceMap5461=true := by decide +kernel
theorem fusedMap5461_checked : acceptsGraphIso
    (fused (graph core5461) (root 5) 0 2) DegreeOneSmallSpectrum133.graph fusedMap5461=true := by decide +kernel
theorem certified5461 : Certified (graph core5461) (root 5) 0 2 :=
  of_native_maps core5461 SmallGeFourSpectrum019.graph DegreeOneSmallSpectrum133.graph
    sourceMap5461 fusedMap5461 sourceMap5461_checked fusedMap5461_checked
    DegreeTwoThreeFiniteComparisons.comparison5461
#print axioms sourceMap5461_checked
#print axioms fusedMap5461_checked
#print axioms certified5461
def sourceMap5461swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,7,8,9,6] (sourceLabel 5 2 0 v)
def fusedMap5461swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap5461swap_checked : acceptsGraphIso
    (source (graph core5461) (root 5) 2 0) SmallGeFourSpectrum019.graph sourceMap5461swap=true := by decide +kernel
theorem fusedMap5461swap_checked : acceptsGraphIso
    (fused (graph core5461) (root 5) 2 0) DegreeOneSmallSpectrum133.graph fusedMap5461swap=true := by decide +kernel
theorem certified5461swap : Certified (graph core5461) (root 5) 2 0 :=
  of_native_maps core5461 SmallGeFourSpectrum019.graph DegreeOneSmallSpectrum133.graph
    sourceMap5461swap fusedMap5461swap sourceMap5461swap_checked fusedMap5461swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5461
#print axioms sourceMap5461swap_checked
#print axioms fusedMap5461swap_checked
#print axioms certified5461swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
