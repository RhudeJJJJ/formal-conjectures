/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2312 : Family 10 := level10.get ⟨999,by decide⟩
def sourceMap2312 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2312 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2312_checked : acceptsGraphIso
    (source (graph core2312) (root 10) 0 0) DegreeOneSmallSpectrum1534.graph sourceMap2312=true := by decide +kernel
theorem fusedMap2312_checked : acceptsGraphIso
    (fused (graph core2312) (root 10) 0 0) DegreeOneSmallSpectrum1536.graph fusedMap2312=true := by decide +kernel
theorem certified2312 : Certified (graph core2312) (root 10) 0 0 :=
  of_native_maps core2312 DegreeOneSmallSpectrum1534.graph DegreeOneSmallSpectrum1536.graph
    sourceMap2312 fusedMap2312 sourceMap2312_checked fusedMap2312_checked
    DegreeOneSmallComparisons.comparison2312
#print axioms sourceMap2312_checked
#print axioms fusedMap2312_checked
#print axioms certified2312
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
