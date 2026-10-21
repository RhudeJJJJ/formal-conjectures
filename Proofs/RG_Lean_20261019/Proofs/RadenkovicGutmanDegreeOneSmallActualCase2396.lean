/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2396 : Family 10 := level10.get ⟨1240,by decide⟩
def sourceMap2396 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2396 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2396_checked : acceptsGraphIso
    (source (graph core2396) (root 10) 0 0) DegreeOneSmallSpectrum1847.graph sourceMap2396=true := by decide +kernel
theorem fusedMap2396_checked : acceptsGraphIso
    (fused (graph core2396) (root 10) 0 0) DegreeOneSmallSpectrum1887.graph fusedMap2396=true := by decide +kernel
theorem certified2396 : Certified (graph core2396) (root 10) 0 0 :=
  of_native_maps core2396 DegreeOneSmallSpectrum1847.graph DegreeOneSmallSpectrum1887.graph
    sourceMap2396 fusedMap2396 sourceMap2396_checked fusedMap2396_checked
    DegreeOneSmallComparisons.comparison2396
#print axioms sourceMap2396_checked
#print axioms fusedMap2396_checked
#print axioms certified2396
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
