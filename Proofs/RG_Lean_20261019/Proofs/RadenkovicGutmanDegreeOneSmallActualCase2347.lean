/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2347 : Family 10 := level10.get ⟨1069,by decide⟩
def sourceMap2347 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2347 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2347_checked : acceptsGraphIso
    (source (graph core2347) (root 10) 0 0) DegreeOneSmallSpectrum1610.graph sourceMap2347=true := by decide +kernel
theorem fusedMap2347_checked : acceptsGraphIso
    (fused (graph core2347) (root 10) 0 0) DegreeOneSmallSpectrum1692.graph fusedMap2347=true := by decide +kernel
theorem certified2347 : Certified (graph core2347) (root 10) 0 0 :=
  of_native_maps core2347 DegreeOneSmallSpectrum1610.graph DegreeOneSmallSpectrum1692.graph
    sourceMap2347 fusedMap2347 sourceMap2347_checked fusedMap2347_checked
    DegreeOneSmallComparisons.comparison2347
#print axioms sourceMap2347_checked
#print axioms fusedMap2347_checked
#print axioms certified2347
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
