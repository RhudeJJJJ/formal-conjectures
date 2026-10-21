/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2113 : Family 10 := level10.get ⟨539,by decide⟩
def sourceMap2113 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2113 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2113_checked : acceptsGraphIso
    (source (graph core2113) (root 10) 0 0) DegreeOneSmallSpectrum1684.graph sourceMap2113=true := by decide +kernel
theorem fusedMap2113_checked : acceptsGraphIso
    (fused (graph core2113) (root 10) 0 0) DegreeOneSmallSpectrum1045.graph fusedMap2113=true := by decide +kernel
theorem certified2113 : Certified (graph core2113) (root 10) 0 0 :=
  of_native_maps core2113 DegreeOneSmallSpectrum1684.graph DegreeOneSmallSpectrum1045.graph
    sourceMap2113 fusedMap2113 sourceMap2113_checked fusedMap2113_checked
    DegreeOneSmallComparisons.comparison2113
#print axioms sourceMap2113_checked
#print axioms fusedMap2113_checked
#print axioms certified2113
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
