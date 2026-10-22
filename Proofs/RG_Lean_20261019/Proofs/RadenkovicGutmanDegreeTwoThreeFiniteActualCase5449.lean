/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5449 : Family 7 := level7.get ⟨94,by decide⟩
def sourceMap5449 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap5449 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap5449_checked : acceptsGraphIso
    (source (graph core5449) (root 7) 0 0) SmallGeFourSpectrum023.graph sourceMap5449=true := by decide +kernel
theorem fusedMap5449_checked : acceptsGraphIso
    (fused (graph core5449) (root 7) 0 0) DegreeOneSmallSpectrum148.graph fusedMap5449=true := by decide +kernel
theorem certified5449 : Certified (graph core5449) (root 7) 0 0 :=
  of_native_maps core5449 SmallGeFourSpectrum023.graph DegreeOneSmallSpectrum148.graph
    sourceMap5449 fusedMap5449 sourceMap5449_checked fusedMap5449_checked
    DegreeTwoThreeFiniteComparisons.comparison5449
#print axioms sourceMap5449_checked
#print axioms fusedMap5449_checked
#print axioms certified5449
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
