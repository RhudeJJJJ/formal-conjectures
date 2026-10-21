/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2297 : Family 10 := level10.get ⟨931,by decide⟩
def sourceMap2297 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2297 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2297_checked : acceptsGraphIso
    (source (graph core2297) (root 10) 0 0) DegreeOneSmallSpectrum1315.graph sourceMap2297=true := by decide +kernel
theorem fusedMap2297_checked : acceptsGraphIso
    (fused (graph core2297) (root 10) 0 0) DegreeOneSmallSpectrum1314.graph fusedMap2297=true := by decide +kernel
theorem certified2297 : Certified (graph core2297) (root 10) 0 0 :=
  of_native_maps core2297 DegreeOneSmallSpectrum1315.graph DegreeOneSmallSpectrum1314.graph
    sourceMap2297 fusedMap2297 sourceMap2297_checked fusedMap2297_checked
    DegreeOneSmallComparisons.comparison2297
#print axioms sourceMap2297_checked
#print axioms fusedMap2297_checked
#print axioms certified2297
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
