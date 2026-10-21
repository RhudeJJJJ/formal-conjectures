/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2065 : Family 10 := level10.get ⟨442,by decide⟩
def sourceMap2065 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2065 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2065_checked : acceptsGraphIso
    (source (graph core2065) (root 10) 0 0) DegreeOneSmallSpectrum1096.graph sourceMap2065=true := by decide +kernel
theorem fusedMap2065_checked : acceptsGraphIso
    (fused (graph core2065) (root 10) 0 0) DegreeOneSmallSpectrum1490.graph fusedMap2065=true := by decide +kernel
theorem certified2065 : Certified (graph core2065) (root 10) 0 0 :=
  of_native_maps core2065 DegreeOneSmallSpectrum1096.graph DegreeOneSmallSpectrum1490.graph
    sourceMap2065 fusedMap2065 sourceMap2065_checked fusedMap2065_checked
    DegreeOneSmallComparisons.comparison2065
#print axioms sourceMap2065_checked
#print axioms fusedMap2065_checked
#print axioms certified2065
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
