/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2170 : Family 10 := level10.get ⟨642,by decide⟩
def sourceMap2170 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2170 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2170_checked : acceptsGraphIso
    (source (graph core2170) (root 10) 0 0) DegreeOneSmallSpectrum1715.graph sourceMap2170=true := by decide +kernel
theorem fusedMap2170_checked : acceptsGraphIso
    (fused (graph core2170) (root 10) 0 0) DegreeOneSmallSpectrum1240.graph fusedMap2170=true := by decide +kernel
theorem certified2170 : Certified (graph core2170) (root 10) 0 0 :=
  of_native_maps core2170 DegreeOneSmallSpectrum1715.graph DegreeOneSmallSpectrum1240.graph
    sourceMap2170 fusedMap2170 sourceMap2170_checked fusedMap2170_checked
    DegreeOneSmallComparisons.comparison2170
#print axioms sourceMap2170_checked
#print axioms fusedMap2170_checked
#print axioms certified2170
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
