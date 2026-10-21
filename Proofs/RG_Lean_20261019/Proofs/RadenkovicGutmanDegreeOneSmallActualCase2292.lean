/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2292 : Family 10 := level10.get ⟨908,by decide⟩
def sourceMap2292 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2292 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2292_checked : acceptsGraphIso
    (source (graph core2292) (root 10) 0 0) DegreeOneSmallSpectrum1783.graph sourceMap2292=true := by decide +kernel
theorem fusedMap2292_checked : acceptsGraphIso
    (fused (graph core2292) (root 10) 0 0) DegreeOneSmallSpectrum1493.graph fusedMap2292=true := by decide +kernel
theorem certified2292 : Certified (graph core2292) (root 10) 0 0 :=
  of_native_maps core2292 DegreeOneSmallSpectrum1783.graph DegreeOneSmallSpectrum1493.graph
    sourceMap2292 fusedMap2292 sourceMap2292_checked fusedMap2292_checked
    DegreeOneSmallComparisons.comparison2292
#print axioms sourceMap2292_checked
#print axioms fusedMap2292_checked
#print axioms certified2292
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
