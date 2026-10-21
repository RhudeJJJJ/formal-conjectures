/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2028 : Family 10 := level10.get ⟨379,by decide⟩
def sourceMap2028 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2028 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2028_checked : acceptsGraphIso
    (source (graph core2028) (root 10) 0 0) DegreeOneSmallSpectrum1176.graph sourceMap2028=true := by decide +kernel
theorem fusedMap2028_checked : acceptsGraphIso
    (fused (graph core2028) (root 10) 0 0) DegreeOneSmallSpectrum1484.graph fusedMap2028=true := by decide +kernel
theorem certified2028 : Certified (graph core2028) (root 10) 0 0 :=
  of_native_maps core2028 DegreeOneSmallSpectrum1176.graph DegreeOneSmallSpectrum1484.graph
    sourceMap2028 fusedMap2028 sourceMap2028_checked fusedMap2028_checked
    DegreeOneSmallComparisons.comparison2028
#print axioms sourceMap2028_checked
#print axioms fusedMap2028_checked
#print axioms certified2028
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
