/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2418 : Family 10 := level10.get ⟨1300,by decide⟩
def sourceMap2418 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (sourceLabel 10 0 0 v)
def fusedMap2418 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2418_checked : acceptsGraphIso
    (source (graph core2418) (root 10) 0 0) DegreeOneSmallSpectrum1765.graph sourceMap2418=true := by decide +kernel
theorem fusedMap2418_checked : acceptsGraphIso
    (fused (graph core2418) (root 10) 0 0) DegreeOneSmallSpectrum1938.graph fusedMap2418=true := by decide +kernel
theorem certified2418 : Certified (graph core2418) (root 10) 0 0 :=
  of_native_maps core2418 DegreeOneSmallSpectrum1765.graph DegreeOneSmallSpectrum1938.graph
    sourceMap2418 fusedMap2418 sourceMap2418_checked fusedMap2418_checked
    DegreeOneSmallComparisons.comparison2418
#print axioms sourceMap2418_checked
#print axioms fusedMap2418_checked
#print axioms certified2418
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
