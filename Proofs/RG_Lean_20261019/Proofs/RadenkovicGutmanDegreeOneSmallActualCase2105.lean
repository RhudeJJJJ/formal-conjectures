/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2105 : Family 10 := level10.get ⟨526,by decide⟩
def sourceMap2105 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2105 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2105_checked : acceptsGraphIso
    (source (graph core2105) (root 10) 0 0) DegreeOneSmallSpectrum1662.graph sourceMap2105=true := by decide +kernel
theorem fusedMap2105_checked : acceptsGraphIso
    (fused (graph core2105) (root 10) 0 0) DegreeOneSmallSpectrum1023.graph fusedMap2105=true := by decide +kernel
theorem certified2105 : Certified (graph core2105) (root 10) 0 0 :=
  of_native_maps core2105 DegreeOneSmallSpectrum1662.graph DegreeOneSmallSpectrum1023.graph
    sourceMap2105 fusedMap2105 sourceMap2105_checked fusedMap2105_checked
    DegreeOneSmallComparisons.comparison2105
#print axioms sourceMap2105_checked
#print axioms fusedMap2105_checked
#print axioms certified2105
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
