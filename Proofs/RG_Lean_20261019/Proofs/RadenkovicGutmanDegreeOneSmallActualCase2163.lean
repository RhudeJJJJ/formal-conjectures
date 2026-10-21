/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2163 : Family 10 := level10.get ⟨628,by decide⟩
def sourceMap2163 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2163 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2163_checked : acceptsGraphIso
    (source (graph core2163) (root 10) 0 0) DegreeOneSmallSpectrum1759.graph sourceMap2163=true := by decide +kernel
theorem fusedMap2163_checked : acceptsGraphIso
    (fused (graph core2163) (root 10) 0 0) DegreeOneSmallSpectrum1208.graph fusedMap2163=true := by decide +kernel
theorem certified2163 : Certified (graph core2163) (root 10) 0 0 :=
  of_native_maps core2163 DegreeOneSmallSpectrum1759.graph DegreeOneSmallSpectrum1208.graph
    sourceMap2163 fusedMap2163 sourceMap2163_checked fusedMap2163_checked
    DegreeOneSmallComparisons.comparison2163
#print axioms sourceMap2163_checked
#print axioms fusedMap2163_checked
#print axioms certified2163
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
