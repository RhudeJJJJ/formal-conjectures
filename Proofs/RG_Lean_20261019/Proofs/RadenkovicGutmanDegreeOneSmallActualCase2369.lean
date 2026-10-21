/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2369 : Family 10 := level10.get ⟨1129,by decide⟩
def sourceMap2369 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (sourceLabel 10 0 0 v)
def fusedMap2369 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2369_checked : acceptsGraphIso
    (source (graph core2369) (root 10) 0 0) DegreeOneSmallSpectrum1756.graph sourceMap2369=true := by decide +kernel
theorem fusedMap2369_checked : acceptsGraphIso
    (fused (graph core2369) (root 10) 0 0) DegreeOneSmallSpectrum1792.graph fusedMap2369=true := by decide +kernel
theorem certified2369 : Certified (graph core2369) (root 10) 0 0 :=
  of_native_maps core2369 DegreeOneSmallSpectrum1756.graph DegreeOneSmallSpectrum1792.graph
    sourceMap2369 fusedMap2369 sourceMap2369_checked fusedMap2369_checked
    DegreeOneSmallComparisons.comparison2369
#print axioms sourceMap2369_checked
#print axioms fusedMap2369_checked
#print axioms certified2369
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
