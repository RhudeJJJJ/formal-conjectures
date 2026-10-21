/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2399 : Family 10 := level10.get ⟨1244,by decide⟩
def sourceMap2399 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (sourceLabel 10 0 0 v)
def fusedMap2399 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2399_checked : acceptsGraphIso
    (source (graph core2399) (root 10) 0 0) DegreeOneSmallSpectrum1761.graph sourceMap2399=true := by decide +kernel
theorem fusedMap2399_checked : acceptsGraphIso
    (fused (graph core2399) (root 10) 0 0) DegreeOneSmallSpectrum1896.graph fusedMap2399=true := by decide +kernel
theorem certified2399 : Certified (graph core2399) (root 10) 0 0 :=
  of_native_maps core2399 DegreeOneSmallSpectrum1761.graph DegreeOneSmallSpectrum1896.graph
    sourceMap2399 fusedMap2399 sourceMap2399_checked fusedMap2399_checked
    DegreeOneSmallComparisons.comparison2399
#print axioms sourceMap2399_checked
#print axioms fusedMap2399_checked
#print axioms certified2399
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
