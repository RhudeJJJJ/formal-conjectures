/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2155 : Family 10 := level10.get ⟨617,by decide⟩
def sourceMap2155 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2155 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2155_checked : acceptsGraphIso
    (source (graph core2155) (root 10) 0 0) DegreeOneSmallSpectrum1841.graph sourceMap2155=true := by decide +kernel
theorem fusedMap2155_checked : acceptsGraphIso
    (fused (graph core2155) (root 10) 0 0) DegreeOneSmallSpectrum1185.graph fusedMap2155=true := by decide +kernel
theorem certified2155 : Certified (graph core2155) (root 10) 0 0 :=
  of_native_maps core2155 DegreeOneSmallSpectrum1841.graph DegreeOneSmallSpectrum1185.graph
    sourceMap2155 fusedMap2155 sourceMap2155_checked fusedMap2155_checked
    DegreeOneSmallComparisons.comparison2155
#print axioms sourceMap2155_checked
#print axioms fusedMap2155_checked
#print axioms certified2155
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
