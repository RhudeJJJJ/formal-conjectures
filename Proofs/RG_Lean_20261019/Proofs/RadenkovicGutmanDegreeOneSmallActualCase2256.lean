/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2256 : Family 10 := level10.get ⟨834,by decide⟩
def sourceMap2256 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2256 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2256_checked : acceptsGraphIso
    (source (graph core2256) (root 10) 0 0) DegreeOneSmallSpectrum1770.graph sourceMap2256=true := by decide +kernel
theorem fusedMap2256_checked : acceptsGraphIso
    (fused (graph core2256) (root 10) 0 0) DegreeOneSmallSpectrum1460.graph fusedMap2256=true := by decide +kernel
theorem certified2256 : Certified (graph core2256) (root 10) 0 0 :=
  of_native_maps core2256 DegreeOneSmallSpectrum1770.graph DegreeOneSmallSpectrum1460.graph
    sourceMap2256 fusedMap2256 sourceMap2256_checked fusedMap2256_checked
    DegreeOneSmallComparisons.comparison2256
#print axioms sourceMap2256_checked
#print axioms fusedMap2256_checked
#print axioms certified2256
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
