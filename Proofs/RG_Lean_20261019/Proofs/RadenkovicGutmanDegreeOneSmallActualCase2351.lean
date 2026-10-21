/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2351 : Family 10 := level10.get ⟨1077,by decide⟩
def sourceMap2351 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2351 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2351_checked : acceptsGraphIso
    (source (graph core2351) (root 10) 0 0) DegreeOneSmallSpectrum1676.graph sourceMap2351=true := by decide +kernel
theorem fusedMap2351_checked : acceptsGraphIso
    (fused (graph core2351) (root 10) 0 0) DegreeOneSmallSpectrum1696.graph fusedMap2351=true := by decide +kernel
theorem certified2351 : Certified (graph core2351) (root 10) 0 0 :=
  of_native_maps core2351 DegreeOneSmallSpectrum1676.graph DegreeOneSmallSpectrum1696.graph
    sourceMap2351 fusedMap2351 sourceMap2351_checked fusedMap2351_checked
    DegreeOneSmallComparisons.comparison2351
#print axioms sourceMap2351_checked
#print axioms fusedMap2351_checked
#print axioms certified2351
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
