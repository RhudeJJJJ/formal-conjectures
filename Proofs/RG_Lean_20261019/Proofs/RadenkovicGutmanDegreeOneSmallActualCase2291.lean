/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2291 : Family 10 := level10.get ⟨904,by decide⟩
def sourceMap2291 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2291 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2291_checked : acceptsGraphIso
    (source (graph core2291) (root 10) 0 0) DegreeOneSmallSpectrum1743.graph sourceMap2291=true := by decide +kernel
theorem fusedMap2291_checked : acceptsGraphIso
    (fused (graph core2291) (root 10) 0 0) DegreeOneSmallSpectrum1480.graph fusedMap2291=true := by decide +kernel
theorem certified2291 : Certified (graph core2291) (root 10) 0 0 :=
  of_native_maps core2291 DegreeOneSmallSpectrum1743.graph DegreeOneSmallSpectrum1480.graph
    sourceMap2291 fusedMap2291 sourceMap2291_checked fusedMap2291_checked
    DegreeOneSmallComparisons.comparison2291
#print axioms sourceMap2291_checked
#print axioms fusedMap2291_checked
#print axioms certified2291
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
