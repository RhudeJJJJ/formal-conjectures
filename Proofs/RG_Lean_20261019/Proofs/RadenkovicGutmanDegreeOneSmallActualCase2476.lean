/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2476 : Family 10 := level10.get ⟨1617,by decide⟩
def sourceMap2476 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2476 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2476_checked : acceptsGraphIso
    (source (graph core2476) (root 10) 0 0) DegreeOneSmallSpectrum2011.graph sourceMap2476=true := by decide +kernel
theorem fusedMap2476_checked : acceptsGraphIso
    (fused (graph core2476) (root 10) 0 0) DegreeOneSmallSpectrum1702.graph fusedMap2476=true := by decide +kernel
theorem certified2476 : Certified (graph core2476) (root 10) 0 0 :=
  of_native_maps core2476 DegreeOneSmallSpectrum2011.graph DegreeOneSmallSpectrum1702.graph
    sourceMap2476 fusedMap2476 sourceMap2476_checked fusedMap2476_checked
    DegreeOneSmallComparisons.comparison2476
#print axioms sourceMap2476_checked
#print axioms fusedMap2476_checked
#print axioms certified2476
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
