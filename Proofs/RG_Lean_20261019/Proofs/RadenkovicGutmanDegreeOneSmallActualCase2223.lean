/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2223 : Family 10 := level10.get ⟨753,by decide⟩
def sourceMap2223 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2223 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2223_checked : acceptsGraphIso
    (source (graph core2223) (root 10) 0 0) DegreeOneSmallSpectrum1751.graph sourceMap2223=true := by decide +kernel
theorem fusedMap2223_checked : acceptsGraphIso
    (fused (graph core2223) (root 10) 0 0) DegreeOneSmallSpectrum1387.graph fusedMap2223=true := by decide +kernel
theorem certified2223 : Certified (graph core2223) (root 10) 0 0 :=
  of_native_maps core2223 DegreeOneSmallSpectrum1751.graph DegreeOneSmallSpectrum1387.graph
    sourceMap2223 fusedMap2223 sourceMap2223_checked fusedMap2223_checked
    DegreeOneSmallComparisons.comparison2223
#print axioms sourceMap2223_checked
#print axioms fusedMap2223_checked
#print axioms certified2223
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
