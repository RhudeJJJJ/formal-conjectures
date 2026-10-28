/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5431 : Family 6 := level6.get ⟨18,by decide⟩
def sourceMap5431 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,2,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap5431 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,6,7,8,4,5,2,3] (fusedLabel 6 0 0 v)
theorem sourceMap5431_checked : acceptsGraphIso
    (source (graph core5431) (root 6) 0 0) SmallGeFourSpectrum006.graph sourceMap5431=true := by decide +kernel
theorem fusedMap5431_checked : acceptsGraphIso
    (fused (graph core5431) (root 6) 0 0) DegreeOneSmallSpectrum058.graph fusedMap5431=true := by decide +kernel
theorem certified5431 : Certified (graph core5431) (root 6) 0 0 :=
  of_native_maps core5431 SmallGeFourSpectrum006.graph DegreeOneSmallSpectrum058.graph
    sourceMap5431 fusedMap5431 sourceMap5431_checked fusedMap5431_checked
    DegreeTwoThreeFiniteComparisons.comparison5431
#print axioms sourceMap5431_checked
#print axioms fusedMap5431_checked
#print axioms certified5431
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
