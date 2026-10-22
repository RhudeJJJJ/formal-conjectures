/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5469 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5469 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 5) → Fin 10 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9] (sourceLabel 3 0 4 v)
def fusedMap5469 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 0 4 v)
theorem sourceMap5469_checked : acceptsGraphIso
    (source (graph core5469) (root 3) 0 4) SmallGeFourSpectrum016.graph sourceMap5469=true := by decide +kernel
theorem fusedMap5469_checked : acceptsGraphIso
    (fused (graph core5469) (root 3) 0 4) DegreeOneSmallSpectrum074.graph fusedMap5469=true := by decide +kernel
theorem certified5469 : Certified (graph core5469) (root 3) 0 4 :=
  of_native_maps core5469 SmallGeFourSpectrum016.graph DegreeOneSmallSpectrum074.graph
    sourceMap5469 fusedMap5469 sourceMap5469_checked fusedMap5469_checked
    DegreeTwoThreeFiniteComparisons.comparison5469
#print axioms sourceMap5469_checked
#print axioms fusedMap5469_checked
#print axioms certified5469
def sourceMap5469swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,7,8,9,6] (sourceLabel 3 4 0 v)
def fusedMap5469swap : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 4 0 v)
theorem sourceMap5469swap_checked : acceptsGraphIso
    (source (graph core5469) (root 3) 4 0) SmallGeFourSpectrum016.graph sourceMap5469swap=true := by decide +kernel
theorem fusedMap5469swap_checked : acceptsGraphIso
    (fused (graph core5469) (root 3) 4 0) DegreeOneSmallSpectrum074.graph fusedMap5469swap=true := by decide +kernel
theorem certified5469swap : Certified (graph core5469) (root 3) 4 0 :=
  of_native_maps core5469 SmallGeFourSpectrum016.graph DegreeOneSmallSpectrum074.graph
    sourceMap5469swap fusedMap5469swap sourceMap5469swap_checked fusedMap5469swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5469
#print axioms sourceMap5469swap_checked
#print axioms fusedMap5469swap_checked
#print axioms certified5469swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
