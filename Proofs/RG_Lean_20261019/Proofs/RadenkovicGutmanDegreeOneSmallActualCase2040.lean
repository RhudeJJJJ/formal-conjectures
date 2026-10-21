/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2040 : Family 10 := level10.get ⟨398,by decide⟩
def sourceMap2040 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2040 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2040_checked : acceptsGraphIso
    (source (graph core2040) (root 10) 0 0) DegreeOneSmallSpectrum1110.graph sourceMap2040=true := by decide +kernel
theorem fusedMap2040_checked : acceptsGraphIso
    (fused (graph core2040) (root 10) 0 0) DegreeOneSmallSpectrum1488.graph fusedMap2040=true := by decide +kernel
theorem certified2040 : Certified (graph core2040) (root 10) 0 0 :=
  of_native_maps core2040 DegreeOneSmallSpectrum1110.graph DegreeOneSmallSpectrum1488.graph
    sourceMap2040 fusedMap2040 sourceMap2040_checked fusedMap2040_checked
    DegreeOneSmallComparisons.comparison2040
#print axioms sourceMap2040_checked
#print axioms fusedMap2040_checked
#print axioms certified2040
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
