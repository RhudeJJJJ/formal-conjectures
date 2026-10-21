/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2072 : Family 10 := level10.get ⟨456,by decide⟩
def sourceMap2072 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,8,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2072 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2072_checked : acceptsGraphIso
    (source (graph core2072) (root 10) 0 0) DegreeOneSmallSpectrum1084.graph sourceMap2072=true := by decide +kernel
theorem fusedMap2072_checked : acceptsGraphIso
    (fused (graph core2072) (root 10) 0 0) DegreeOneSmallSpectrum1475.graph fusedMap2072=true := by decide +kernel
theorem certified2072 : Certified (graph core2072) (root 10) 0 0 :=
  of_native_maps core2072 DegreeOneSmallSpectrum1084.graph DegreeOneSmallSpectrum1475.graph
    sourceMap2072 fusedMap2072 sourceMap2072_checked fusedMap2072_checked
    DegreeOneSmallComparisons.comparison2072
#print axioms sourceMap2072_checked
#print axioms fusedMap2072_checked
#print axioms certified2072
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
