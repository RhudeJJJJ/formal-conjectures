/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2387 : Family 10 := level10.get ⟨1181,by decide⟩
def sourceMap2387 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2387 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2387_checked : acceptsGraphIso
    (source (graph core2387) (root 10) 0 0) DegreeOneSmallSpectrum1880.graph sourceMap2387=true := by decide +kernel
theorem fusedMap2387_checked : acceptsGraphIso
    (fused (graph core2387) (root 10) 0 0) DegreeOneSmallSpectrum1876.graph fusedMap2387=true := by decide +kernel
theorem certified2387 : Certified (graph core2387) (root 10) 0 0 :=
  of_native_maps core2387 DegreeOneSmallSpectrum1880.graph DegreeOneSmallSpectrum1876.graph
    sourceMap2387 fusedMap2387 sourceMap2387_checked fusedMap2387_checked
    DegreeOneSmallComparisons.comparison2387
#print axioms sourceMap2387_checked
#print axioms fusedMap2387_checked
#print axioms certified2387
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
