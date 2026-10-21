/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2451 : Family 10 := level10.get ⟨1428,by decide⟩
def sourceMap2451 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,4,5,6,7,8,9,2,3] (sourceLabel 10 0 0 v)
def fusedMap2451 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2451_checked : acceptsGraphIso
    (source (graph core2451) (root 10) 0 0) DegreeOneSmallSpectrum1702.graph sourceMap2451=true := by decide +kernel
theorem fusedMap2451_checked : acceptsGraphIso
    (fused (graph core2451) (root 10) 0 0) DegreeOneSmallSpectrum1982.graph fusedMap2451=true := by decide +kernel
theorem certified2451 : Certified (graph core2451) (root 10) 0 0 :=
  of_native_maps core2451 DegreeOneSmallSpectrum1702.graph DegreeOneSmallSpectrum1982.graph
    sourceMap2451 fusedMap2451 sourceMap2451_checked fusedMap2451_checked
    DegreeOneSmallComparisons.comparison2451
#print axioms sourceMap2451_checked
#print axioms fusedMap2451_checked
#print axioms certified2451
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
