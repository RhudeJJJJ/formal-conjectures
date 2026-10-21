/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2394 : Family 10 := level10.get ⟨1196,by decide⟩
def sourceMap2394 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (sourceLabel 10 0 0 v)
def fusedMap2394 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2394_checked : acceptsGraphIso
    (source (graph core2394) (root 10) 0 0) DegreeOneSmallSpectrum1735.graph sourceMap2394=true := by decide +kernel
theorem fusedMap2394_checked : acceptsGraphIso
    (fused (graph core2394) (root 10) 0 0) DegreeOneSmallSpectrum1883.graph fusedMap2394=true := by decide +kernel
theorem certified2394 : Certified (graph core2394) (root 10) 0 0 :=
  of_native_maps core2394 DegreeOneSmallSpectrum1735.graph DegreeOneSmallSpectrum1883.graph
    sourceMap2394 fusedMap2394 sourceMap2394_checked fusedMap2394_checked
    DegreeOneSmallComparisons.comparison2394
#print axioms sourceMap2394_checked
#print axioms fusedMap2394_checked
#print axioms certified2394
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
