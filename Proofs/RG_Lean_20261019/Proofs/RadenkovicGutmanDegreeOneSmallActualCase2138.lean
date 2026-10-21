/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2138 : Family 10 := level10.get ⟨583,by decide⟩
def sourceMap2138 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 10 0 0 v)
def fusedMap2138 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2138_checked : acceptsGraphIso
    (source (graph core2138) (root 10) 0 0) DegreeOneSmallSpectrum1795.graph sourceMap2138=true := by decide +kernel
theorem fusedMap2138_checked : acceptsGraphIso
    (fused (graph core2138) (root 10) 0 0) DegreeOneSmallSpectrum1123.graph fusedMap2138=true := by decide +kernel
theorem certified2138 : Certified (graph core2138) (root 10) 0 0 :=
  of_native_maps core2138 DegreeOneSmallSpectrum1795.graph DegreeOneSmallSpectrum1123.graph
    sourceMap2138 fusedMap2138 sourceMap2138_checked fusedMap2138_checked
    DegreeOneSmallComparisons.comparison2138
#print axioms sourceMap2138_checked
#print axioms fusedMap2138_checked
#print axioms certified2138
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
