/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2240 : Family 10 := level10.get ⟨788,by decide⟩
def sourceMap2240 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,6,0,1,2,3,4,5,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2240 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2240_checked : acceptsGraphIso
    (source (graph core2240) (root 10) 0 0) DegreeOneSmallSpectrum1428.graph sourceMap2240=true := by decide +kernel
theorem fusedMap2240_checked : acceptsGraphIso
    (fused (graph core2240) (root 10) 0 0) DegreeOneSmallSpectrum1427.graph fusedMap2240=true := by decide +kernel
theorem certified2240 : Certified (graph core2240) (root 10) 0 0 :=
  of_native_maps core2240 DegreeOneSmallSpectrum1428.graph DegreeOneSmallSpectrum1427.graph
    sourceMap2240 fusedMap2240 sourceMap2240_checked fusedMap2240_checked
    DegreeOneSmallComparisons.comparison2240
#print axioms sourceMap2240_checked
#print axioms fusedMap2240_checked
#print axioms certified2240
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
