/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2172 : Family 10 := level10.get ⟨645,by decide⟩
def sourceMap2172 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2172 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2172_checked : acceptsGraphIso
    (source (graph core2172) (root 10) 0 0) DegreeOneSmallSpectrum1786.graph sourceMap2172=true := by decide +kernel
theorem fusedMap2172_checked : acceptsGraphIso
    (fused (graph core2172) (root 10) 0 0) DegreeOneSmallSpectrum1243.graph fusedMap2172=true := by decide +kernel
theorem certified2172 : Certified (graph core2172) (root 10) 0 0 :=
  of_native_maps core2172 DegreeOneSmallSpectrum1786.graph DegreeOneSmallSpectrum1243.graph
    sourceMap2172 fusedMap2172 sourceMap2172_checked fusedMap2172_checked
    DegreeOneSmallComparisons.comparison2172
#print axioms sourceMap2172_checked
#print axioms fusedMap2172_checked
#print axioms certified2172
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
