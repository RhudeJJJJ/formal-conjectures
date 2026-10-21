/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2132 : Family 10 := level10.get ⟨573,by decide⟩
def sourceMap2132 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2132 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2132_checked : acceptsGraphIso
    (source (graph core2132) (root 10) 0 0) DegreeOneSmallSpectrum1757.graph sourceMap2132=true := by decide +kernel
theorem fusedMap2132_checked : acceptsGraphIso
    (fused (graph core2132) (root 10) 0 0) DegreeOneSmallSpectrum1110.graph fusedMap2132=true := by decide +kernel
theorem certified2132 : Certified (graph core2132) (root 10) 0 0 :=
  of_native_maps core2132 DegreeOneSmallSpectrum1757.graph DegreeOneSmallSpectrum1110.graph
    sourceMap2132 fusedMap2132 sourceMap2132_checked fusedMap2132_checked
    DegreeOneSmallComparisons.comparison2132
#print axioms sourceMap2132_checked
#print axioms fusedMap2132_checked
#print axioms certified2132
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
