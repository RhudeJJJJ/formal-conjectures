/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2442 : Family 10 := level10.get ⟨1406,by decide⟩
def sourceMap2442 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2442 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2442_checked : acceptsGraphIso
    (source (graph core2442) (root 10) 0 0) DegreeOneSmallSpectrum1980.graph sourceMap2442=true := by decide +kernel
theorem fusedMap2442_checked : acceptsGraphIso
    (fused (graph core2442) (root 10) 0 0) DegreeOneSmallSpectrum1973.graph fusedMap2442=true := by decide +kernel
theorem certified2442 : Certified (graph core2442) (root 10) 0 0 :=
  of_native_maps core2442 DegreeOneSmallSpectrum1980.graph DegreeOneSmallSpectrum1973.graph
    sourceMap2442 fusedMap2442 sourceMap2442_checked fusedMap2442_checked
    DegreeOneSmallComparisons.comparison2442
#print axioms sourceMap2442_checked
#print axioms fusedMap2442_checked
#print axioms certified2442
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
