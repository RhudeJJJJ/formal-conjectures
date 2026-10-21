/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2270 : Family 10 := level10.get ⟨858,by decide⟩
def sourceMap2270 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2270 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2270_checked : acceptsGraphIso
    (source (graph core2270) (root 10) 0 0) DegreeOneSmallSpectrum1772.graph sourceMap2270=true := by decide +kernel
theorem fusedMap2270_checked : acceptsGraphIso
    (fused (graph core2270) (root 10) 0 0) DegreeOneSmallSpectrum1482.graph fusedMap2270=true := by decide +kernel
theorem certified2270 : Certified (graph core2270) (root 10) 0 0 :=
  of_native_maps core2270 DegreeOneSmallSpectrum1772.graph DegreeOneSmallSpectrum1482.graph
    sourceMap2270 fusedMap2270 sourceMap2270_checked fusedMap2270_checked
    DegreeOneSmallComparisons.comparison2270
#print axioms sourceMap2270_checked
#print axioms fusedMap2270_checked
#print axioms certified2270
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
