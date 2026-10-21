/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2377 : Family 10 := level10.get ⟨1148,by decide⟩
def sourceMap2377 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2377 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2377_checked : acceptsGraphIso
    (source (graph core2377) (root 10) 0 0) DegreeOneSmallSpectrum1835.graph sourceMap2377=true := by decide +kernel
theorem fusedMap2377_checked : acceptsGraphIso
    (fused (graph core2377) (root 10) 0 0) DegreeOneSmallSpectrum1833.graph fusedMap2377=true := by decide +kernel
theorem certified2377 : Certified (graph core2377) (root 10) 0 0 :=
  of_native_maps core2377 DegreeOneSmallSpectrum1835.graph DegreeOneSmallSpectrum1833.graph
    sourceMap2377 fusedMap2377 sourceMap2377_checked fusedMap2377_checked
    DegreeOneSmallComparisons.comparison2377
#print axioms sourceMap2377_checked
#print axioms fusedMap2377_checked
#print axioms certified2377
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
