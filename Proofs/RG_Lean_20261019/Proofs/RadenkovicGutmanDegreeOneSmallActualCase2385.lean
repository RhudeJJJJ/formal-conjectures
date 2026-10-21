/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2385 : Family 10 := level10.get ⟨1178,by decide⟩
def sourceMap2385 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2385 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2385_checked : acceptsGraphIso
    (source (graph core2385) (root 10) 0 0) DegreeOneSmallSpectrum1866.graph sourceMap2385=true := by decide +kernel
theorem fusedMap2385_checked : acceptsGraphIso
    (fused (graph core2385) (root 10) 0 0) DegreeOneSmallSpectrum1865.graph fusedMap2385=true := by decide +kernel
theorem certified2385 : Certified (graph core2385) (root 10) 0 0 :=
  of_native_maps core2385 DegreeOneSmallSpectrum1866.graph DegreeOneSmallSpectrum1865.graph
    sourceMap2385 fusedMap2385 sourceMap2385_checked fusedMap2385_checked
    DegreeOneSmallComparisons.comparison2385
#print axioms sourceMap2385_checked
#print axioms fusedMap2385_checked
#print axioms certified2385
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
