/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2106 : Family 10 := level10.get ⟨527,by decide⟩
def sourceMap2106 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 10 0 0 v)
def fusedMap2106 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2106_checked : acceptsGraphIso
    (source (graph core2106) (root 10) 0 0) DegreeOneSmallSpectrum1660.graph sourceMap2106=true := by decide +kernel
theorem fusedMap2106_checked : acceptsGraphIso
    (fused (graph core2106) (root 10) 0 0) DegreeOneSmallSpectrum1026.graph fusedMap2106=true := by decide +kernel
theorem certified2106 : Certified (graph core2106) (root 10) 0 0 :=
  of_native_maps core2106 DegreeOneSmallSpectrum1660.graph DegreeOneSmallSpectrum1026.graph
    sourceMap2106 fusedMap2106 sourceMap2106_checked fusedMap2106_checked
    DegreeOneSmallComparisons.comparison2106
#print axioms sourceMap2106_checked
#print axioms fusedMap2106_checked
#print axioms certified2106
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
