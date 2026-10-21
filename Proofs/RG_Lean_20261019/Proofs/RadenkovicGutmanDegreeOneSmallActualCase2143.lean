/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2143 : Family 10 := level10.get ⟨592,by decide⟩
def sourceMap2143 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2143 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2143_checked : acceptsGraphIso
    (source (graph core2143) (root 10) 0 0) DegreeOneSmallSpectrum1815.graph sourceMap2143=true := by decide +kernel
theorem fusedMap2143_checked : acceptsGraphIso
    (fused (graph core2143) (root 10) 0 0) DegreeOneSmallSpectrum1138.graph fusedMap2143=true := by decide +kernel
theorem certified2143 : Certified (graph core2143) (root 10) 0 0 :=
  of_native_maps core2143 DegreeOneSmallSpectrum1815.graph DegreeOneSmallSpectrum1138.graph
    sourceMap2143 fusedMap2143 sourceMap2143_checked fusedMap2143_checked
    DegreeOneSmallComparisons.comparison2143
#print axioms sourceMap2143_checked
#print axioms fusedMap2143_checked
#print axioms certified2143
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
