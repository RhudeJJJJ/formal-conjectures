/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2120 : Family 10 := level10.get ⟨551,by decide⟩
def sourceMap2120 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2120 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2120_checked : acceptsGraphIso
    (source (graph core2120) (root 10) 0 0) DegreeOneSmallSpectrum1677.graph sourceMap2120=true := by decide +kernel
theorem fusedMap2120_checked : acceptsGraphIso
    (fused (graph core2120) (root 10) 0 0) DegreeOneSmallSpectrum1078.graph fusedMap2120=true := by decide +kernel
theorem certified2120 : Certified (graph core2120) (root 10) 0 0 :=
  of_native_maps core2120 DegreeOneSmallSpectrum1677.graph DegreeOneSmallSpectrum1078.graph
    sourceMap2120 fusedMap2120 sourceMap2120_checked fusedMap2120_checked
    DegreeOneSmallComparisons.comparison2120
#print axioms sourceMap2120_checked
#print axioms fusedMap2120_checked
#print axioms certified2120
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
