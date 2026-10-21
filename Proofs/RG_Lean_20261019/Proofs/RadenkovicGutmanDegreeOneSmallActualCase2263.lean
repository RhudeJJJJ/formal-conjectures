/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2263 : Family 10 := level10.get ⟨845,by decide⟩
def sourceMap2263 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2263 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2263_checked : acceptsGraphIso
    (source (graph core2263) (root 10) 0 0) DegreeOneSmallSpectrum1835.graph sourceMap2263=true := by decide +kernel
theorem fusedMap2263_checked : acceptsGraphIso
    (fused (graph core2263) (root 10) 0 0) DegreeOneSmallSpectrum1470.graph fusedMap2263=true := by decide +kernel
theorem certified2263 : Certified (graph core2263) (root 10) 0 0 :=
  of_native_maps core2263 DegreeOneSmallSpectrum1835.graph DegreeOneSmallSpectrum1470.graph
    sourceMap2263 fusedMap2263 sourceMap2263_checked fusedMap2263_checked
    DegreeOneSmallComparisons.comparison2263
#print axioms sourceMap2263_checked
#print axioms fusedMap2263_checked
#print axioms certified2263
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
