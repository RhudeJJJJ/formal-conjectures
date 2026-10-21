/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2022 : Family 10 := level10.get ⟨372,by decide⟩
def sourceMap2022 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2022 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2022_checked : acceptsGraphIso
    (source (graph core2022) (root 10) 0 0) DegreeOneSmallSpectrum1277.graph sourceMap2022=true := by decide +kernel
theorem fusedMap2022_checked : acceptsGraphIso
    (fused (graph core2022) (root 10) 0 0) DegreeOneSmallSpectrum1471.graph fusedMap2022=true := by decide +kernel
theorem certified2022 : Certified (graph core2022) (root 10) 0 0 :=
  of_native_maps core2022 DegreeOneSmallSpectrum1277.graph DegreeOneSmallSpectrum1471.graph
    sourceMap2022 fusedMap2022 sourceMap2022_checked fusedMap2022_checked
    DegreeOneSmallComparisons.comparison2022
#print axioms sourceMap2022_checked
#print axioms fusedMap2022_checked
#print axioms certified2022
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
