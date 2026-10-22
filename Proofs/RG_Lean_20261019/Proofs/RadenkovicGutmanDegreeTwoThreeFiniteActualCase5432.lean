/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5432 : Family 6 := level6.get ⟨26,by decide⟩
def sourceMap5432 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,2,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap5432 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![4,0,1,2,3,7,8,5,6] (fusedLabel 6 0 0 v)
theorem sourceMap5432_checked : acceptsGraphIso
    (source (graph core5432) (root 6) 0 0) DegreeOneSmallSpectrum065.graph sourceMap5432=true := by decide +kernel
theorem fusedMap5432_checked : acceptsGraphIso
    (fused (graph core5432) (root 6) 0 0) DegreeOneSmallSpectrum050.graph fusedMap5432=true := by decide +kernel
theorem certified5432 : Certified (graph core5432) (root 6) 0 0 :=
  of_native_maps core5432 DegreeOneSmallSpectrum065.graph DegreeOneSmallSpectrum050.graph
    sourceMap5432 fusedMap5432 sourceMap5432_checked fusedMap5432_checked
    DegreeTwoThreeFiniteComparisons.comparison5432
#print axioms sourceMap5432_checked
#print axioms fusedMap5432_checked
#print axioms certified5432
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
