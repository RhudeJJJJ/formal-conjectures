/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2018 : Family 10 := level10.get ⟨367,by decide⟩
def sourceMap2018 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2018 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2018_checked : acceptsGraphIso
    (source (graph core2018) (root 10) 0 0) DegreeOneSmallSpectrum1274.graph sourceMap2018=true := by decide +kernel
theorem fusedMap2018_checked : acceptsGraphIso
    (fused (graph core2018) (root 10) 0 0) DegreeOneSmallSpectrum1459.graph fusedMap2018=true := by decide +kernel
theorem certified2018 : Certified (graph core2018) (root 10) 0 0 :=
  of_native_maps core2018 DegreeOneSmallSpectrum1274.graph DegreeOneSmallSpectrum1459.graph
    sourceMap2018 fusedMap2018 sourceMap2018_checked fusedMap2018_checked
    DegreeOneSmallComparisons.comparison2018
#print axioms sourceMap2018_checked
#print axioms fusedMap2018_checked
#print axioms certified2018
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
