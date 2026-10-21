/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2160 : Family 10 := level10.get ⟨624,by decide⟩
def sourceMap2160 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2160 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2160_checked : acceptsGraphIso
    (source (graph core2160) (root 10) 0 0) DegreeOneSmallSpectrum1844.graph sourceMap2160=true := by decide +kernel
theorem fusedMap2160_checked : acceptsGraphIso
    (fused (graph core2160) (root 10) 0 0) DegreeOneSmallSpectrum1196.graph fusedMap2160=true := by decide +kernel
theorem certified2160 : Certified (graph core2160) (root 10) 0 0 :=
  of_native_maps core2160 DegreeOneSmallSpectrum1844.graph DegreeOneSmallSpectrum1196.graph
    sourceMap2160 fusedMap2160 sourceMap2160_checked fusedMap2160_checked
    DegreeOneSmallComparisons.comparison2160
#print axioms sourceMap2160_checked
#print axioms fusedMap2160_checked
#print axioms certified2160
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
