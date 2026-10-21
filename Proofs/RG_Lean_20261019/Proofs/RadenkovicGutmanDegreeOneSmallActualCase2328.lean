/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2328 : Family 10 := level10.get ⟨1032,by decide⟩
def sourceMap2328 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2328 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2328_checked : acceptsGraphIso
    (source (graph core2328) (root 10) 0 0) DegreeOneSmallSpectrum1602.graph sourceMap2328=true := by decide +kernel
theorem fusedMap2328_checked : acceptsGraphIso
    (fused (graph core2328) (root 10) 0 0) DegreeOneSmallSpectrum1604.graph fusedMap2328=true := by decide +kernel
theorem certified2328 : Certified (graph core2328) (root 10) 0 0 :=
  of_native_maps core2328 DegreeOneSmallSpectrum1602.graph DegreeOneSmallSpectrum1604.graph
    sourceMap2328 fusedMap2328 sourceMap2328_checked fusedMap2328_checked
    DegreeOneSmallComparisons.comparison2328
#print axioms sourceMap2328_checked
#print axioms fusedMap2328_checked
#print axioms certified2328
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
