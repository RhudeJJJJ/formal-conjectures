/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2384 : Family 10 := level10.get ⟨1177,by decide⟩
def sourceMap2384 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2384 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2384_checked : acceptsGraphIso
    (source (graph core2384) (root 10) 0 0) DegreeOneSmallSpectrum1857.graph sourceMap2384=true := by decide +kernel
theorem fusedMap2384_checked : acceptsGraphIso
    (fused (graph core2384) (root 10) 0 0) DegreeOneSmallSpectrum1856.graph fusedMap2384=true := by decide +kernel
theorem certified2384 : Certified (graph core2384) (root 10) 0 0 :=
  of_native_maps core2384 DegreeOneSmallSpectrum1857.graph DegreeOneSmallSpectrum1856.graph
    sourceMap2384 fusedMap2384 sourceMap2384_checked fusedMap2384_checked
    DegreeOneSmallComparisons.comparison2384
#print axioms sourceMap2384_checked
#print axioms fusedMap2384_checked
#print axioms certified2384
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
