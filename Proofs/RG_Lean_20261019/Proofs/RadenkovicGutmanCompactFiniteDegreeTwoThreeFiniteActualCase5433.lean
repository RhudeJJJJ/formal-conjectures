/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5433 : Family 6 := level6.get ⟨32,by decide⟩
def sourceMap5433 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,2,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap5433 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,5,6,7,8,3,4,1,2] (fusedLabel 6 0 0 v)
theorem sourceMap5433_checked : acceptsGraphIso
    (source (graph core5433) (root 6) 0 0) DegreeOneSmallSpectrum066.graph sourceMap5433=true := by decide +kernel
theorem fusedMap5433_checked : acceptsGraphIso
    (fused (graph core5433) (root 6) 0 0) DegreeOneSmallSpectrum057.graph fusedMap5433=true := by decide +kernel
theorem certified5433 : Certified (graph core5433) (root 6) 0 0 :=
  of_native_maps core5433 DegreeOneSmallSpectrum066.graph DegreeOneSmallSpectrum057.graph
    sourceMap5433 fusedMap5433 sourceMap5433_checked fusedMap5433_checked
    DegreeTwoThreeFiniteComparisons.comparison5433
#print axioms sourceMap5433_checked
#print axioms fusedMap5433_checked
#print axioms certified5433
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
