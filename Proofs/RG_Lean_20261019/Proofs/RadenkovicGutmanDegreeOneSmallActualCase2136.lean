/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2136 : Family 10 := level10.get ⟨581,by decide⟩
def sourceMap2136 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2136 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2136_checked : acceptsGraphIso
    (source (graph core2136) (root 10) 0 0) DegreeOneSmallSpectrum1796.graph sourceMap2136=true := by decide +kernel
theorem fusedMap2136_checked : acceptsGraphIso
    (fused (graph core2136) (root 10) 0 0) DegreeOneSmallSpectrum1119.graph fusedMap2136=true := by decide +kernel
theorem certified2136 : Certified (graph core2136) (root 10) 0 0 :=
  of_native_maps core2136 DegreeOneSmallSpectrum1796.graph DegreeOneSmallSpectrum1119.graph
    sourceMap2136 fusedMap2136 sourceMap2136_checked fusedMap2136_checked
    DegreeOneSmallComparisons.comparison2136
#print axioms sourceMap2136_checked
#print axioms fusedMap2136_checked
#print axioms certified2136
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
