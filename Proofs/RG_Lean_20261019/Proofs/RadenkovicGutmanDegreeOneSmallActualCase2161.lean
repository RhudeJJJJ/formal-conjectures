/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2161 : Family 10 := level10.get ⟨625,by decide⟩
def sourceMap2161 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2161 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2161_checked : acceptsGraphIso
    (source (graph core2161) (root 10) 0 0) DegreeOneSmallSpectrum1845.graph sourceMap2161=true := by decide +kernel
theorem fusedMap2161_checked : acceptsGraphIso
    (fused (graph core2161) (root 10) 0 0) DegreeOneSmallSpectrum1197.graph fusedMap2161=true := by decide +kernel
theorem certified2161 : Certified (graph core2161) (root 10) 0 0 :=
  of_native_maps core2161 DegreeOneSmallSpectrum1845.graph DegreeOneSmallSpectrum1197.graph
    sourceMap2161 fusedMap2161 sourceMap2161_checked fusedMap2161_checked
    DegreeOneSmallComparisons.comparison2161
#print axioms sourceMap2161_checked
#print axioms fusedMap2161_checked
#print axioms certified2161
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
