/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2440 : Family 10 := level10.get ⟨1370,by decide⟩
def sourceMap2440 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (sourceLabel 10 0 0 v)
def fusedMap2440 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2440_checked : acceptsGraphIso
    (source (graph core2440) (root 10) 0 0) DegreeOneSmallSpectrum1776.graph sourceMap2440=true := by decide +kernel
theorem fusedMap2440_checked : acceptsGraphIso
    (fused (graph core2440) (root 10) 0 0) DegreeOneSmallSpectrum1971.graph fusedMap2440=true := by decide +kernel
theorem certified2440 : Certified (graph core2440) (root 10) 0 0 :=
  of_native_maps core2440 DegreeOneSmallSpectrum1776.graph DegreeOneSmallSpectrum1971.graph
    sourceMap2440 fusedMap2440 sourceMap2440_checked fusedMap2440_checked
    DegreeOneSmallComparisons.comparison2440
#print axioms sourceMap2440_checked
#print axioms fusedMap2440_checked
#print axioms certified2440
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
