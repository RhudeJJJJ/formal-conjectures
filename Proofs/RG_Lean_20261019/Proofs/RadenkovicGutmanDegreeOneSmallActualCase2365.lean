/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2365 : Family 10 := level10.get ⟨1116,by decide⟩
def sourceMap2365 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2365 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2365_checked : acceptsGraphIso
    (source (graph core2365) (root 10) 0 0) DegreeOneSmallSpectrum1744.graph sourceMap2365=true := by decide +kernel
theorem fusedMap2365_checked : acceptsGraphIso
    (fused (graph core2365) (root 10) 0 0) DegreeOneSmallSpectrum1772.graph fusedMap2365=true := by decide +kernel
theorem certified2365 : Certified (graph core2365) (root 10) 0 0 :=
  of_native_maps core2365 DegreeOneSmallSpectrum1744.graph DegreeOneSmallSpectrum1772.graph
    sourceMap2365 fusedMap2365 sourceMap2365_checked fusedMap2365_checked
    DegreeOneSmallComparisons.comparison2365
#print axioms sourceMap2365_checked
#print axioms fusedMap2365_checked
#print axioms certified2365
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
