/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2107 : Family 10 := level10.get ⟨529,by decide⟩
def sourceMap2107 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2107 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2107_checked : acceptsGraphIso
    (source (graph core2107) (root 10) 0 0) DegreeOneSmallSpectrum1657.graph sourceMap2107=true := by decide +kernel
theorem fusedMap2107_checked : acceptsGraphIso
    (fused (graph core2107) (root 10) 0 0) DegreeOneSmallSpectrum1034.graph fusedMap2107=true := by decide +kernel
theorem certified2107 : Certified (graph core2107) (root 10) 0 0 :=
  of_native_maps core2107 DegreeOneSmallSpectrum1657.graph DegreeOneSmallSpectrum1034.graph
    sourceMap2107 fusedMap2107 sourceMap2107_checked fusedMap2107_checked
    DegreeOneSmallComparisons.comparison2107
#print axioms sourceMap2107_checked
#print axioms fusedMap2107_checked
#print axioms certified2107
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
