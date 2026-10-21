/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2207 : Family 10 := level10.get ⟨727,by decide⟩
def sourceMap2207 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2207 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2207_checked : acceptsGraphIso
    (source (graph core2207) (root 10) 0 0) DegreeOneSmallSpectrum1825.graph sourceMap2207=true := by decide +kernel
theorem fusedMap2207_checked : acceptsGraphIso
    (fused (graph core2207) (root 10) 0 0) DegreeOneSmallSpectrum1352.graph fusedMap2207=true := by decide +kernel
theorem certified2207 : Certified (graph core2207) (root 10) 0 0 :=
  of_native_maps core2207 DegreeOneSmallSpectrum1825.graph DegreeOneSmallSpectrum1352.graph
    sourceMap2207 fusedMap2207 sourceMap2207_checked fusedMap2207_checked
    DegreeOneSmallComparisons.comparison2207
#print axioms sourceMap2207_checked
#print axioms fusedMap2207_checked
#print axioms certified2207
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
