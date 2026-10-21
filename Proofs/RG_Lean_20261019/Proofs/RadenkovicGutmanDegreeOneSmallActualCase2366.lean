/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2366 : Family 10 := level10.get ⟨1118,by decide⟩
def sourceMap2366 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2366 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2366_checked : acceptsGraphIso
    (source (graph core2366) (root 10) 0 0) DegreeOneSmallSpectrum1756.graph sourceMap2366=true := by decide +kernel
theorem fusedMap2366_checked : acceptsGraphIso
    (fused (graph core2366) (root 10) 0 0) DegreeOneSmallSpectrum1773.graph fusedMap2366=true := by decide +kernel
theorem certified2366 : Certified (graph core2366) (root 10) 0 0 :=
  of_native_maps core2366 DegreeOneSmallSpectrum1756.graph DegreeOneSmallSpectrum1773.graph
    sourceMap2366 fusedMap2366 sourceMap2366_checked fusedMap2366_checked
    DegreeOneSmallComparisons.comparison2366
#print axioms sourceMap2366_checked
#print axioms fusedMap2366_checked
#print axioms certified2366
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
