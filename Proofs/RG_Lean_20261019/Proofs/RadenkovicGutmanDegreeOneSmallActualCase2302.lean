/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2302 : Family 10 := level10.get ⟨940,by decide⟩
def sourceMap2302 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,1,0,10,11,12,2,3,4,5,6,8,9] (sourceLabel 10 0 0 v)
def fusedMap2302 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2302_checked : acceptsGraphIso
    (source (graph core2302) (root 10) 0 0) DegreeOneSmallSpectrum1558.graph sourceMap2302=true := by decide +kernel
theorem fusedMap2302_checked : acceptsGraphIso
    (fused (graph core2302) (root 10) 0 0) DegreeOneSmallSpectrum1464.graph fusedMap2302=true := by decide +kernel
theorem certified2302 : Certified (graph core2302) (root 10) 0 0 :=
  of_native_maps core2302 DegreeOneSmallSpectrum1558.graph DegreeOneSmallSpectrum1464.graph
    sourceMap2302 fusedMap2302 sourceMap2302_checked fusedMap2302_checked
    DegreeOneSmallComparisons.comparison2302
#print axioms sourceMap2302_checked
#print axioms fusedMap2302_checked
#print axioms certified2302
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
