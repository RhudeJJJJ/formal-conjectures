/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2295 : Family 10 := level10.get ⟨928,by decide⟩
def sourceMap2295 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2295 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2295_checked : acceptsGraphIso
    (source (graph core2295) (root 10) 0 0) DegreeOneSmallSpectrum1137.graph sourceMap2295=true := by decide +kernel
theorem fusedMap2295_checked : acceptsGraphIso
    (fused (graph core2295) (root 10) 0 0) DegreeOneSmallSpectrum1136.graph fusedMap2295=true := by decide +kernel
theorem certified2295 : Certified (graph core2295) (root 10) 0 0 :=
  of_native_maps core2295 DegreeOneSmallSpectrum1137.graph DegreeOneSmallSpectrum1136.graph
    sourceMap2295 fusedMap2295 sourceMap2295_checked fusedMap2295_checked
    DegreeOneSmallComparisons.comparison2295
#print axioms sourceMap2295_checked
#print axioms fusedMap2295_checked
#print axioms certified2295
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
