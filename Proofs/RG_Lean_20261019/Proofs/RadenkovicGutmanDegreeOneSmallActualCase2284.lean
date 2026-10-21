/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2284 : Family 10 := level10.get ⟨895,by decide⟩
def sourceMap2284 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2284 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2284_checked : acceptsGraphIso
    (source (graph core2284) (root 10) 0 0) DegreeOneSmallSpectrum1505.graph sourceMap2284=true := by decide +kernel
theorem fusedMap2284_checked : acceptsGraphIso
    (fused (graph core2284) (root 10) 0 0) DegreeOneSmallSpectrum1504.graph fusedMap2284=true := by decide +kernel
theorem certified2284 : Certified (graph core2284) (root 10) 0 0 :=
  of_native_maps core2284 DegreeOneSmallSpectrum1505.graph DegreeOneSmallSpectrum1504.graph
    sourceMap2284 fusedMap2284 sourceMap2284_checked fusedMap2284_checked
    DegreeOneSmallComparisons.comparison2284
#print axioms sourceMap2284_checked
#print axioms fusedMap2284_checked
#print axioms certified2284
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
