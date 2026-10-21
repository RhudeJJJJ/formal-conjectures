/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2021 : Family 10 := level10.get ⟨371,by decide⟩
def sourceMap2021 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2021 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2021_checked : acceptsGraphIso
    (source (graph core2021) (root 10) 0 0) DegreeOneSmallSpectrum1276.graph sourceMap2021=true := by decide +kernel
theorem fusedMap2021_checked : acceptsGraphIso
    (fused (graph core2021) (root 10) 0 0) DegreeOneSmallSpectrum1467.graph fusedMap2021=true := by decide +kernel
theorem certified2021 : Certified (graph core2021) (root 10) 0 0 :=
  of_native_maps core2021 DegreeOneSmallSpectrum1276.graph DegreeOneSmallSpectrum1467.graph
    sourceMap2021 fusedMap2021 sourceMap2021_checked fusedMap2021_checked
    DegreeOneSmallComparisons.comparison2021
#print axioms sourceMap2021_checked
#print axioms fusedMap2021_checked
#print axioms certified2021
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
