/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5442 : Family 7 := level7.get ⟨60,by decide⟩
def sourceMap5442 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap5442 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,7,8,9,2,3,6,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap5442_checked : acceptsGraphIso
    (source (graph core5442) (root 7) 0 0) SmallGeFourSpectrum022.graph sourceMap5442=true := by decide +kernel
theorem fusedMap5442_checked : acceptsGraphIso
    (fused (graph core5442) (root 7) 0 0) DegreeOneSmallSpectrum133.graph fusedMap5442=true := by decide +kernel
theorem certified5442 : Certified (graph core5442) (root 7) 0 0 :=
  of_native_maps core5442 SmallGeFourSpectrum022.graph DegreeOneSmallSpectrum133.graph
    sourceMap5442 fusedMap5442 sourceMap5442_checked fusedMap5442_checked
    DegreeTwoThreeFiniteComparisons.comparison5442
#print axioms sourceMap5442_checked
#print axioms fusedMap5442_checked
#print axioms certified5442
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
