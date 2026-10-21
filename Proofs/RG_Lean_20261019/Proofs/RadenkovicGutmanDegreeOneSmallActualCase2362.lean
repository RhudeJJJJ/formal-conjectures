/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2362 : Family 10 := level10.get ⟨1110,by decide⟩
def sourceMap2362 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2362 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2362_checked : acceptsGraphIso
    (source (graph core2362) (root 10) 0 0) DegreeOneSmallSpectrum1745.graph sourceMap2362=true := by decide +kernel
theorem fusedMap2362_checked : acceptsGraphIso
    (fused (graph core2362) (root 10) 0 0) DegreeOneSmallSpectrum1754.graph fusedMap2362=true := by decide +kernel
theorem certified2362 : Certified (graph core2362) (root 10) 0 0 :=
  of_native_maps core2362 DegreeOneSmallSpectrum1745.graph DegreeOneSmallSpectrum1754.graph
    sourceMap2362 fusedMap2362 sourceMap2362_checked fusedMap2362_checked
    DegreeOneSmallComparisons.comparison2362
#print axioms sourceMap2362_checked
#print axioms fusedMap2362_checked
#print axioms certified2362
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
