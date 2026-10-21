/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2371 : Family 10 := level10.get ⟨1134,by decide⟩
def sourceMap2371 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2371 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2371_checked : acceptsGraphIso
    (source (graph core2371) (root 10) 0 0) DegreeOneSmallSpectrum1808.graph sourceMap2371=true := by decide +kernel
theorem fusedMap2371_checked : acceptsGraphIso
    (fused (graph core2371) (root 10) 0 0) DegreeOneSmallSpectrum1807.graph fusedMap2371=true := by decide +kernel
theorem certified2371 : Certified (graph core2371) (root 10) 0 0 :=
  of_native_maps core2371 DegreeOneSmallSpectrum1808.graph DegreeOneSmallSpectrum1807.graph
    sourceMap2371 fusedMap2371 sourceMap2371_checked fusedMap2371_checked
    DegreeOneSmallComparisons.comparison2371
#print axioms sourceMap2371_checked
#print axioms fusedMap2371_checked
#print axioms certified2371
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
