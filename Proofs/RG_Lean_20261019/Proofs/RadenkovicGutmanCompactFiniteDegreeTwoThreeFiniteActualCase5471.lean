/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5471 : Family 5 := level5.get ⟨12,by decide⟩
def sourceMap5471 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap5471 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap5471_checked : acceptsGraphIso
    (source (graph core5471) (root 5) 0 4) SmallGeFourSpectrum110.graph sourceMap5471=true := by decide +kernel
theorem fusedMap5471_checked : acceptsGraphIso
    (fused (graph core5471) (root 5) 0 4) DegreeOneSmallSpectrum388.graph fusedMap5471=true := by decide +kernel
theorem certified5471 : Certified (graph core5471) (root 5) 0 4 :=
  of_native_maps core5471 SmallGeFourSpectrum110.graph DegreeOneSmallSpectrum388.graph
    sourceMap5471 fusedMap5471 sourceMap5471_checked fusedMap5471_checked
    DegreeTwoThreeFiniteComparisons.comparison5471
#print axioms sourceMap5471_checked
#print axioms fusedMap5471_checked
#print axioms certified5471
def sourceMap5471swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap5471swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap5471swap_checked : acceptsGraphIso
    (source (graph core5471) (root 5) 4 0) SmallGeFourSpectrum110.graph sourceMap5471swap=true := by decide +kernel
theorem fusedMap5471swap_checked : acceptsGraphIso
    (fused (graph core5471) (root 5) 4 0) DegreeOneSmallSpectrum388.graph fusedMap5471swap=true := by decide +kernel
theorem certified5471swap : Certified (graph core5471) (root 5) 4 0 :=
  of_native_maps core5471 SmallGeFourSpectrum110.graph DegreeOneSmallSpectrum388.graph
    sourceMap5471swap fusedMap5471swap sourceMap5471swap_checked fusedMap5471swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5471
#print axioms sourceMap5471swap_checked
#print axioms fusedMap5471swap_checked
#print axioms certified5471swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
