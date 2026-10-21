/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2303 : Family 10 := level10.get ⟨941,by decide⟩
def sourceMap2303 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,1,0,10,11,12,2,3,4,5,9,7,8] (sourceLabel 10 0 0 v)
def fusedMap2303 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2303_checked : acceptsGraphIso
    (source (graph core2303) (root 10) 0 0) DegreeOneSmallSpectrum1609.graph sourceMap2303=true := by decide +kernel
theorem fusedMap2303_checked : acceptsGraphIso
    (fused (graph core2303) (root 10) 0 0) DegreeOneSmallSpectrum1465.graph fusedMap2303=true := by decide +kernel
theorem certified2303 : Certified (graph core2303) (root 10) 0 0 :=
  of_native_maps core2303 DegreeOneSmallSpectrum1609.graph DegreeOneSmallSpectrum1465.graph
    sourceMap2303 fusedMap2303 sourceMap2303_checked fusedMap2303_checked
    DegreeOneSmallComparisons.comparison2303
#print axioms sourceMap2303_checked
#print axioms fusedMap2303_checked
#print axioms certified2303
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
