/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2278 : Family 10 := level10.get ⟨878,by decide⟩
def sourceMap2278 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2278 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2278_checked : acceptsGraphIso
    (source (graph core2278) (root 10) 0 0) DegreeOneSmallSpectrum1773.graph sourceMap2278=true := by decide +kernel
theorem fusedMap2278_checked : acceptsGraphIso
    (fused (graph core2278) (root 10) 0 0) DegreeOneSmallSpectrum1487.graph fusedMap2278=true := by decide +kernel
theorem certified2278 : Certified (graph core2278) (root 10) 0 0 :=
  of_native_maps core2278 DegreeOneSmallSpectrum1773.graph DegreeOneSmallSpectrum1487.graph
    sourceMap2278 fusedMap2278 sourceMap2278_checked fusedMap2278_checked
    DegreeOneSmallComparisons.comparison2278
#print axioms sourceMap2278_checked
#print axioms fusedMap2278_checked
#print axioms certified2278
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
