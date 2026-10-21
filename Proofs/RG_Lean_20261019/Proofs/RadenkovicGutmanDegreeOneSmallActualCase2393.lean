/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2393 : Family 10 := level10.get ⟨1194,by decide⟩
def sourceMap2393 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (sourceLabel 10 0 0 v)
def fusedMap2393 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2393_checked : acceptsGraphIso
    (source (graph core2393) (root 10) 0 0) DegreeOneSmallSpectrum1725.graph sourceMap2393=true := by decide +kernel
theorem fusedMap2393_checked : acceptsGraphIso
    (fused (graph core2393) (root 10) 0 0) DegreeOneSmallSpectrum1882.graph fusedMap2393=true := by decide +kernel
theorem certified2393 : Certified (graph core2393) (root 10) 0 0 :=
  of_native_maps core2393 DegreeOneSmallSpectrum1725.graph DegreeOneSmallSpectrum1882.graph
    sourceMap2393 fusedMap2393 sourceMap2393_checked fusedMap2393_checked
    DegreeOneSmallComparisons.comparison2393
#print axioms sourceMap2393_checked
#print axioms fusedMap2393_checked
#print axioms certified2393
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
