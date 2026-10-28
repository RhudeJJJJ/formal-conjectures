/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5466 : Family 6 := level6.get ⟨40,by decide⟩
def sourceMap5466 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap5466 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap5466_checked : acceptsGraphIso
    (source (graph core5466) (root 6) 0 2) SmallGeFourSpectrum045.graph sourceMap5466=true := by decide +kernel
theorem fusedMap5466_checked : acceptsGraphIso
    (fused (graph core5466) (root 6) 0 2) DegreeOneSmallSpectrum253.graph fusedMap5466=true := by decide +kernel
theorem certified5466 : Certified (graph core5466) (root 6) 0 2 :=
  of_native_maps core5466 SmallGeFourSpectrum045.graph DegreeOneSmallSpectrum253.graph
    sourceMap5466 fusedMap5466 sourceMap5466_checked fusedMap5466_checked
    DegreeTwoThreeFiniteComparisons.comparison5466
#print axioms sourceMap5466_checked
#print axioms fusedMap5466_checked
#print axioms certified5466
def sourceMap5466swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap5466swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap5466swap_checked : acceptsGraphIso
    (source (graph core5466) (root 6) 2 0) SmallGeFourSpectrum045.graph sourceMap5466swap=true := by decide +kernel
theorem fusedMap5466swap_checked : acceptsGraphIso
    (fused (graph core5466) (root 6) 2 0) DegreeOneSmallSpectrum253.graph fusedMap5466swap=true := by decide +kernel
theorem certified5466swap : Certified (graph core5466) (root 6) 2 0 :=
  of_native_maps core5466 SmallGeFourSpectrum045.graph DegreeOneSmallSpectrum253.graph
    sourceMap5466swap fusedMap5466swap sourceMap5466swap_checked fusedMap5466swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5466
#print axioms sourceMap5466swap_checked
#print axioms fusedMap5466swap_checked
#print axioms certified5466swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
