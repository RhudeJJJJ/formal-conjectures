/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2382 : Family 10 := level10.get ⟨1158,by decide⟩
def sourceMap2382 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2382 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2382_checked : acceptsGraphIso
    (source (graph core2382) (root 10) 0 0) DegreeOneSmallSpectrum1778.graph sourceMap2382=true := by decide +kernel
theorem fusedMap2382_checked : acceptsGraphIso
    (fused (graph core2382) (root 10) 0 0) DegreeOneSmallSpectrum1838.graph fusedMap2382=true := by decide +kernel
theorem certified2382 : Certified (graph core2382) (root 10) 0 0 :=
  of_native_maps core2382 DegreeOneSmallSpectrum1778.graph DegreeOneSmallSpectrum1838.graph
    sourceMap2382 fusedMap2382 sourceMap2382_checked fusedMap2382_checked
    DegreeOneSmallComparisons.comparison2382
#print axioms sourceMap2382_checked
#print axioms fusedMap2382_checked
#print axioms certified2382
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
