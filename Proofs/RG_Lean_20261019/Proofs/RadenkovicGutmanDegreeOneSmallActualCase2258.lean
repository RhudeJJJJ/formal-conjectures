/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2258 : Family 10 := level10.get ⟨839,by decide⟩
def sourceMap2258 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2258 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2258_checked : acceptsGraphIso
    (source (graph core2258) (root 10) 0 0) DegreeOneSmallSpectrum1878.graph sourceMap2258=true := by decide +kernel
theorem fusedMap2258_checked : acceptsGraphIso
    (fused (graph core2258) (root 10) 0 0) DegreeOneSmallSpectrum1464.graph fusedMap2258=true := by decide +kernel
theorem certified2258 : Certified (graph core2258) (root 10) 0 0 :=
  of_native_maps core2258 DegreeOneSmallSpectrum1878.graph DegreeOneSmallSpectrum1464.graph
    sourceMap2258 fusedMap2258 sourceMap2258_checked fusedMap2258_checked
    DegreeOneSmallComparisons.comparison2258
#print axioms sourceMap2258_checked
#print axioms fusedMap2258_checked
#print axioms certified2258
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
