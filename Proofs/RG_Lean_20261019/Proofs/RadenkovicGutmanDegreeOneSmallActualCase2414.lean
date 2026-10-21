/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2414 : Family 10 := level10.get ⟨1276,by decide⟩
def sourceMap2414 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2414 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2414_checked : acceptsGraphIso
    (source (graph core2414) (root 10) 0 0) DegreeOneSmallSpectrum1740.graph sourceMap2414=true := by decide +kernel
theorem fusedMap2414_checked : acceptsGraphIso
    (fused (graph core2414) (root 10) 0 0) DegreeOneSmallSpectrum1930.graph fusedMap2414=true := by decide +kernel
theorem certified2414 : Certified (graph core2414) (root 10) 0 0 :=
  of_native_maps core2414 DegreeOneSmallSpectrum1740.graph DegreeOneSmallSpectrum1930.graph
    sourceMap2414 fusedMap2414 sourceMap2414_checked fusedMap2414_checked
    DegreeOneSmallComparisons.comparison2414
#print axioms sourceMap2414_checked
#print axioms fusedMap2414_checked
#print axioms certified2414
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
