/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2198 : Family 10 := level10.get ⟨706,by decide⟩
def sourceMap2198 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2198 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2198_checked : acceptsGraphIso
    (source (graph core2198) (root 10) 0 0) DegreeOneSmallSpectrum1823.graph sourceMap2198=true := by decide +kernel
theorem fusedMap2198_checked : acceptsGraphIso
    (fused (graph core2198) (root 10) 0 0) DegreeOneSmallSpectrum1322.graph fusedMap2198=true := by decide +kernel
theorem certified2198 : Certified (graph core2198) (root 10) 0 0 :=
  of_native_maps core2198 DegreeOneSmallSpectrum1823.graph DegreeOneSmallSpectrum1322.graph
    sourceMap2198 fusedMap2198 sourceMap2198_checked fusedMap2198_checked
    DegreeOneSmallComparisons.comparison2198
#print axioms sourceMap2198_checked
#print axioms fusedMap2198_checked
#print axioms certified2198
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
