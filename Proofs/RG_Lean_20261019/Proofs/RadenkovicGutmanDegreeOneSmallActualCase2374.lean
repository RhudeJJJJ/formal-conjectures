/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2374 : Family 10 := level10.get ⟨1138,by decide⟩
def sourceMap2374 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2374 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2374_checked : acceptsGraphIso
    (source (graph core2374) (root 10) 0 0) DegreeOneSmallSpectrum1784.graph sourceMap2374=true := by decide +kernel
theorem fusedMap2374_checked : acceptsGraphIso
    (fused (graph core2374) (root 10) 0 0) DegreeOneSmallSpectrum1810.graph fusedMap2374=true := by decide +kernel
theorem certified2374 : Certified (graph core2374) (root 10) 0 0 :=
  of_native_maps core2374 DegreeOneSmallSpectrum1784.graph DegreeOneSmallSpectrum1810.graph
    sourceMap2374 fusedMap2374 sourceMap2374_checked fusedMap2374_checked
    DegreeOneSmallComparisons.comparison2374
#print axioms sourceMap2374_checked
#print axioms fusedMap2374_checked
#print axioms certified2374
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
