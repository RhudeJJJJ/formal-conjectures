/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2341 : Family 10 := level10.get ⟨1054,by decide⟩
def sourceMap2341 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2341 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2341_checked : acceptsGraphIso
    (source (graph core2341) (root 10) 0 0) DegreeOneSmallSpectrum1655.graph sourceMap2341=true := by decide +kernel
theorem fusedMap2341_checked : acceptsGraphIso
    (fused (graph core2341) (root 10) 0 0) DegreeOneSmallSpectrum1667.graph fusedMap2341=true := by decide +kernel
theorem certified2341 : Certified (graph core2341) (root 10) 0 0 :=
  of_native_maps core2341 DegreeOneSmallSpectrum1655.graph DegreeOneSmallSpectrum1667.graph
    sourceMap2341 fusedMap2341 sourceMap2341_checked fusedMap2341_checked
    DegreeOneSmallComparisons.comparison2341
#print axioms sourceMap2341_checked
#print axioms fusedMap2341_checked
#print axioms certified2341
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
