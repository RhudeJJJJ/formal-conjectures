/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5352 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5352 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,6,7,2,3,4,5,0,8,9,10,11,12] (sourceLabel 2 3 5 v)
def fusedMap5352 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 3 5 v)
theorem sourceMap5352_checked : acceptsGraphIso
    (source (graph core5352) (root 2) 3 5) DegreeOneSmallSpectrum974.graph sourceMap5352=true := by decide +kernel
theorem fusedMap5352_checked : acceptsGraphIso
    (fused (graph core5352) (root 2) 3 5) DegreeOneSmallSpectrum856.graph fusedMap5352=true := by decide +kernel
theorem certified5352 : Certified (graph core5352) (root 2) 3 5 :=
  of_native_maps core5352 DegreeOneSmallSpectrum974.graph DegreeOneSmallSpectrum856.graph
    sourceMap5352 fusedMap5352 sourceMap5352_checked fusedMap5352_checked
    DegreeTwoThreeFiniteComparisons.comparison5352
#print axioms sourceMap5352_checked
#print axioms fusedMap5352_checked
#print axioms certified5352
def sourceMap5352swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,6,7,0,8,9,10,11,12,2,3,4,5] (sourceLabel 2 5 3 v)
def fusedMap5352swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 5 3 v)
theorem sourceMap5352swap_checked : acceptsGraphIso
    (source (graph core5352) (root 2) 5 3) DegreeOneSmallSpectrum974.graph sourceMap5352swap=true := by decide +kernel
theorem fusedMap5352swap_checked : acceptsGraphIso
    (fused (graph core5352) (root 2) 5 3) DegreeOneSmallSpectrum856.graph fusedMap5352swap=true := by decide +kernel
theorem certified5352swap : Certified (graph core5352) (root 2) 5 3 :=
  of_native_maps core5352 DegreeOneSmallSpectrum974.graph DegreeOneSmallSpectrum856.graph
    sourceMap5352swap fusedMap5352swap sourceMap5352swap_checked fusedMap5352swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5352
#print axioms sourceMap5352swap_checked
#print axioms fusedMap5352swap_checked
#print axioms certified5352swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
