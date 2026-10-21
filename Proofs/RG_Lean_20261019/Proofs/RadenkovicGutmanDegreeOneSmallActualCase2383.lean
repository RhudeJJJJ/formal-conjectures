/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2383 : Family 10 := level10.get ⟨1175,by decide⟩
def sourceMap2383 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2383 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2383_checked : acceptsGraphIso
    (source (graph core2383) (root 10) 0 0) DegreeOneSmallSpectrum1843.graph sourceMap2383=true := by decide +kernel
theorem fusedMap2383_checked : acceptsGraphIso
    (fused (graph core2383) (root 10) 0 0) DegreeOneSmallSpectrum1841.graph fusedMap2383=true := by decide +kernel
theorem certified2383 : Certified (graph core2383) (root 10) 0 0 :=
  of_native_maps core2383 DegreeOneSmallSpectrum1843.graph DegreeOneSmallSpectrum1841.graph
    sourceMap2383 fusedMap2383 sourceMap2383_checked fusedMap2383_checked
    DegreeOneSmallComparisons.comparison2383
#print axioms sourceMap2383_checked
#print axioms fusedMap2383_checked
#print axioms certified2383
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
