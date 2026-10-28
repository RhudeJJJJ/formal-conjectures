/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5476 : Family 6 := level6.get ⟨32,by decide⟩
def sourceMap5476 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap5476 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap5476_checked : acceptsGraphIso
    (source (graph core5476) (root 6) 0 4) DegreeOneSmallSpectrum1418.graph sourceMap5476=true := by decide +kernel
theorem fusedMap5476_checked : acceptsGraphIso
    (fused (graph core5476) (root 6) 0 4) DegreeOneSmallSpectrum924.graph fusedMap5476=true := by decide +kernel
theorem certified5476 : Certified (graph core5476) (root 6) 0 4 :=
  of_native_maps core5476 DegreeOneSmallSpectrum1418.graph DegreeOneSmallSpectrum924.graph
    sourceMap5476 fusedMap5476 sourceMap5476_checked fusedMap5476_checked
    DegreeTwoThreeFiniteComparisons.comparison5476
#print axioms sourceMap5476_checked
#print axioms fusedMap5476_checked
#print axioms certified5476
def sourceMap5476swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap5476swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap5476swap_checked : acceptsGraphIso
    (source (graph core5476) (root 6) 4 0) DegreeOneSmallSpectrum1418.graph sourceMap5476swap=true := by decide +kernel
theorem fusedMap5476swap_checked : acceptsGraphIso
    (fused (graph core5476) (root 6) 4 0) DegreeOneSmallSpectrum924.graph fusedMap5476swap=true := by decide +kernel
theorem certified5476swap : Certified (graph core5476) (root 6) 4 0 :=
  of_native_maps core5476 DegreeOneSmallSpectrum1418.graph DegreeOneSmallSpectrum924.graph
    sourceMap5476swap fusedMap5476swap sourceMap5476swap_checked fusedMap5476swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5476
#print axioms sourceMap5476swap_checked
#print axioms fusedMap5476swap_checked
#print axioms certified5476swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
