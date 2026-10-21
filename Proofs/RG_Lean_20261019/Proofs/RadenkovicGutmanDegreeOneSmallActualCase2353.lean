/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2353 : Family 10 := level10.get ⟨1095,by decide⟩
def sourceMap2353 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2353 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2353_checked : acceptsGraphIso
    (source (graph core2353) (root 10) 0 0) DegreeOneSmallSpectrum1703.graph sourceMap2353=true := by decide +kernel
theorem fusedMap2353_checked : acceptsGraphIso
    (fused (graph core2353) (root 10) 0 0) DegreeOneSmallSpectrum1705.graph fusedMap2353=true := by decide +kernel
theorem certified2353 : Certified (graph core2353) (root 10) 0 0 :=
  of_native_maps core2353 DegreeOneSmallSpectrum1703.graph DegreeOneSmallSpectrum1705.graph
    sourceMap2353 fusedMap2353 sourceMap2353_checked fusedMap2353_checked
    DegreeOneSmallComparisons.comparison2353
#print axioms sourceMap2353_checked
#print axioms fusedMap2353_checked
#print axioms certified2353
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
