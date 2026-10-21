/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2088 : Family 10 := level10.get ⟨502,by decide⟩
def sourceMap2088 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2088 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2088_checked : acceptsGraphIso
    (source (graph core2088) (root 10) 0 0) DegreeOneSmallSpectrum1565.graph sourceMap2088=true := by decide +kernel
theorem fusedMap2088_checked : acceptsGraphIso
    (fused (graph core2088) (root 10) 0 0) DegreeOneSmallSpectrum986.graph fusedMap2088=true := by decide +kernel
theorem certified2088 : Certified (graph core2088) (root 10) 0 0 :=
  of_native_maps core2088 DegreeOneSmallSpectrum1565.graph DegreeOneSmallSpectrum986.graph
    sourceMap2088 fusedMap2088 sourceMap2088_checked fusedMap2088_checked
    DegreeOneSmallComparisons.comparison2088
#print axioms sourceMap2088_checked
#print axioms fusedMap2088_checked
#print axioms certified2088
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
