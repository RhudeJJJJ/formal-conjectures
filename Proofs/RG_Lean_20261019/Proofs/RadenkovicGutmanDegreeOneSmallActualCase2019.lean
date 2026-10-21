/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2019 : Family 10 := level10.get ⟨368,by decide⟩
def sourceMap2019 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2019 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2019_checked : acceptsGraphIso
    (source (graph core2019) (root 10) 0 0) DegreeOneSmallSpectrum1239.graph sourceMap2019=true := by decide +kernel
theorem fusedMap2019_checked : acceptsGraphIso
    (fused (graph core2019) (root 10) 0 0) DegreeOneSmallSpectrum1463.graph fusedMap2019=true := by decide +kernel
theorem certified2019 : Certified (graph core2019) (root 10) 0 0 :=
  of_native_maps core2019 DegreeOneSmallSpectrum1239.graph DegreeOneSmallSpectrum1463.graph
    sourceMap2019 fusedMap2019 sourceMap2019_checked fusedMap2019_checked
    DegreeOneSmallComparisons.comparison2019
#print axioms sourceMap2019_checked
#print axioms fusedMap2019_checked
#print axioms certified2019
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
