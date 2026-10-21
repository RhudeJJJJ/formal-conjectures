/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2211 : Family 10 := level10.get ⟨733,by decide⟩
def sourceMap2211 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2211 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2211_checked : acceptsGraphIso
    (source (graph core2211) (root 10) 0 0) DegreeOneSmallSpectrum1766.graph sourceMap2211=true := by decide +kernel
theorem fusedMap2211_checked : acceptsGraphIso
    (fused (graph core2211) (root 10) 0 0) DegreeOneSmallSpectrum1361.graph fusedMap2211=true := by decide +kernel
theorem certified2211 : Certified (graph core2211) (root 10) 0 0 :=
  of_native_maps core2211 DegreeOneSmallSpectrum1766.graph DegreeOneSmallSpectrum1361.graph
    sourceMap2211 fusedMap2211 sourceMap2211_checked fusedMap2211_checked
    DegreeOneSmallComparisons.comparison2211
#print axioms sourceMap2211_checked
#print axioms fusedMap2211_checked
#print axioms certified2211
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
