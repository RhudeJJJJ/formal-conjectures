/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2281 : Family 10 := level10.get ⟨884,by decide⟩
def sourceMap2281 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2281 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2281_checked : acceptsGraphIso
    (source (graph core2281) (root 10) 0 0) DegreeOneSmallSpectrum1722.graph sourceMap2281=true := by decide +kernel
theorem fusedMap2281_checked : acceptsGraphIso
    (fused (graph core2281) (root 10) 0 0) DegreeOneSmallSpectrum1473.graph fusedMap2281=true := by decide +kernel
theorem certified2281 : Certified (graph core2281) (root 10) 0 0 :=
  of_native_maps core2281 DegreeOneSmallSpectrum1722.graph DegreeOneSmallSpectrum1473.graph
    sourceMap2281 fusedMap2281 sourceMap2281_checked fusedMap2281_checked
    DegreeOneSmallComparisons.comparison2281
#print axioms sourceMap2281_checked
#print axioms fusedMap2281_checked
#print axioms certified2281
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
