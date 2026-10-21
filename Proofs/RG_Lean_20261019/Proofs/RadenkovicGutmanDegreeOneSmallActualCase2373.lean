/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2373 : Family 10 := level10.get ⟨1136,by decide⟩
def sourceMap2373 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2373 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2373_checked : acceptsGraphIso
    (source (graph core2373) (root 10) 0 0) DegreeOneSmallSpectrum1745.graph sourceMap2373=true := by decide +kernel
theorem fusedMap2373_checked : acceptsGraphIso
    (fused (graph core2373) (root 10) 0 0) DegreeOneSmallSpectrum1809.graph fusedMap2373=true := by decide +kernel
theorem certified2373 : Certified (graph core2373) (root 10) 0 0 :=
  of_native_maps core2373 DegreeOneSmallSpectrum1745.graph DegreeOneSmallSpectrum1809.graph
    sourceMap2373 fusedMap2373 sourceMap2373_checked fusedMap2373_checked
    DegreeOneSmallComparisons.comparison2373
#print axioms sourceMap2373_checked
#print axioms fusedMap2373_checked
#print axioms certified2373
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
