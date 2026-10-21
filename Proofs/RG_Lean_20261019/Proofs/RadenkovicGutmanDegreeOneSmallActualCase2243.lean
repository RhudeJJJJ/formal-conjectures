/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2243 : Family 10 := level10.get ⟨792,by decide⟩
def sourceMap2243 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2243 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2243_checked : acceptsGraphIso
    (source (graph core2243) (root 10) 0 0) DegreeOneSmallSpectrum1791.graph sourceMap2243=true := by decide +kernel
theorem fusedMap2243_checked : acceptsGraphIso
    (fused (graph core2243) (root 10) 0 0) DegreeOneSmallSpectrum1431.graph fusedMap2243=true := by decide +kernel
theorem certified2243 : Certified (graph core2243) (root 10) 0 0 :=
  of_native_maps core2243 DegreeOneSmallSpectrum1791.graph DegreeOneSmallSpectrum1431.graph
    sourceMap2243 fusedMap2243 sourceMap2243_checked fusedMap2243_checked
    DegreeOneSmallComparisons.comparison2243
#print axioms sourceMap2243_checked
#print axioms fusedMap2243_checked
#print axioms certified2243
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
