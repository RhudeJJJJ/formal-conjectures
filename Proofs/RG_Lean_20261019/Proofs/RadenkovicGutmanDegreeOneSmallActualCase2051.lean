/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2051 : Family 10 := level10.get ⟨417,by decide⟩
def sourceMap2051 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2051 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2051_checked : acceptsGraphIso
    (source (graph core2051) (root 10) 0 0) DegreeOneSmallSpectrum1087.graph sourceMap2051=true := by decide +kernel
theorem fusedMap2051_checked : acceptsGraphIso
    (fused (graph core2051) (root 10) 0 0) DegreeOneSmallSpectrum1474.graph fusedMap2051=true := by decide +kernel
theorem certified2051 : Certified (graph core2051) (root 10) 0 0 :=
  of_native_maps core2051 DegreeOneSmallSpectrum1087.graph DegreeOneSmallSpectrum1474.graph
    sourceMap2051 fusedMap2051 sourceMap2051_checked fusedMap2051_checked
    DegreeOneSmallComparisons.comparison2051
#print axioms sourceMap2051_checked
#print axioms fusedMap2051_checked
#print axioms certified2051
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
