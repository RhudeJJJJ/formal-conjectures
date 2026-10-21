/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2423 : Family 10 := level10.get ⟨1309,by decide⟩
def sourceMap2423 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2423 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2423_checked : acceptsGraphIso
    (source (graph core2423) (root 10) 0 0) DegreeOneSmallSpectrum1789.graph sourceMap2423=true := by decide +kernel
theorem fusedMap2423_checked : acceptsGraphIso
    (fused (graph core2423) (root 10) 0 0) DegreeOneSmallSpectrum1945.graph fusedMap2423=true := by decide +kernel
theorem certified2423 : Certified (graph core2423) (root 10) 0 0 :=
  of_native_maps core2423 DegreeOneSmallSpectrum1789.graph DegreeOneSmallSpectrum1945.graph
    sourceMap2423 fusedMap2423 sourceMap2423_checked fusedMap2423_checked
    DegreeOneSmallComparisons.comparison2423
#print axioms sourceMap2423_checked
#print axioms fusedMap2423_checked
#print axioms certified2423
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
