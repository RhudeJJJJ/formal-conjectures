/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5460 : Family 5 := level5.get ⟨16,by decide⟩
def sourceMap5460 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 0 2 v)
def fusedMap5460 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap5460_checked : acceptsGraphIso
    (source (graph core5460) (root 5) 0 2) SmallGeFourSpectrum017.graph sourceMap5460=true := by decide +kernel
theorem fusedMap5460_checked : acceptsGraphIso
    (fused (graph core5460) (root 5) 0 2) DegreeOneSmallSpectrum115.graph fusedMap5460=true := by decide +kernel
theorem certified5460 : Certified (graph core5460) (root 5) 0 2 :=
  of_native_maps core5460 SmallGeFourSpectrum017.graph DegreeOneSmallSpectrum115.graph
    sourceMap5460 fusedMap5460 sourceMap5460_checked fusedMap5460_checked
    DegreeTwoThreeFiniteComparisons.comparison5460
#print axioms sourceMap5460_checked
#print axioms fusedMap5460_checked
#print axioms certified5460
def sourceMap5460swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,7,8,9,6] (sourceLabel 5 2 0 v)
def fusedMap5460swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap5460swap_checked : acceptsGraphIso
    (source (graph core5460) (root 5) 2 0) SmallGeFourSpectrum017.graph sourceMap5460swap=true := by decide +kernel
theorem fusedMap5460swap_checked : acceptsGraphIso
    (fused (graph core5460) (root 5) 2 0) DegreeOneSmallSpectrum115.graph fusedMap5460swap=true := by decide +kernel
theorem certified5460swap : Certified (graph core5460) (root 5) 2 0 :=
  of_native_maps core5460 SmallGeFourSpectrum017.graph DegreeOneSmallSpectrum115.graph
    sourceMap5460swap fusedMap5460swap sourceMap5460swap_checked fusedMap5460swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5460
#print axioms sourceMap5460swap_checked
#print axioms fusedMap5460swap_checked
#print axioms certified5460swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
