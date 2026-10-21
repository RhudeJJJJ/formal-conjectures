/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2378 : Family 10 := level10.get ⟨1150,by decide⟩
def sourceMap2378 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2378 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2378_checked : acceptsGraphIso
    (source (graph core2378) (root 10) 0 0) DegreeOneSmallSpectrum1611.graph sourceMap2378=true := by decide +kernel
theorem fusedMap2378_checked : acceptsGraphIso
    (fused (graph core2378) (root 10) 0 0) DegreeOneSmallSpectrum1834.graph fusedMap2378=true := by decide +kernel
theorem certified2378 : Certified (graph core2378) (root 10) 0 0 :=
  of_native_maps core2378 DegreeOneSmallSpectrum1611.graph DegreeOneSmallSpectrum1834.graph
    sourceMap2378 fusedMap2378 sourceMap2378_checked fusedMap2378_checked
    DegreeOneSmallComparisons.comparison2378
#print axioms sourceMap2378_checked
#print axioms fusedMap2378_checked
#print axioms certified2378
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
