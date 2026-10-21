/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2045 : Family 10 := level10.get ⟨406,by decide⟩
def sourceMap2045 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2045 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2045_checked : acceptsGraphIso
    (source (graph core2045) (root 10) 0 0) DegreeOneSmallSpectrum1141.graph sourceMap2045=true := by decide +kernel
theorem fusedMap2045_checked : acceptsGraphIso
    (fused (graph core2045) (root 10) 0 0) DegreeOneSmallSpectrum1502.graph fusedMap2045=true := by decide +kernel
theorem certified2045 : Certified (graph core2045) (root 10) 0 0 :=
  of_native_maps core2045 DegreeOneSmallSpectrum1141.graph DegreeOneSmallSpectrum1502.graph
    sourceMap2045 fusedMap2045 sourceMap2045_checked fusedMap2045_checked
    DegreeOneSmallComparisons.comparison2045
#print axioms sourceMap2045_checked
#print axioms fusedMap2045_checked
#print axioms certified2045
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
