/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0326 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0326 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0326 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0326_checked : acceptsGraphIso
    (source (graph core0326) (root 6) 1 1) DegreeOneSmallSpectrum295.graph sourceMap0326=true := by decide +kernel
theorem fusedMap0326_checked : acceptsGraphIso
    (fused (graph core0326) (root 6) 1 1) DegreeOneSmallSpectrum182.graph fusedMap0326=true := by decide +kernel
theorem certified0326 : Certified (graph core0326) (root 6) 1 1 :=
  of_native_maps core0326 DegreeOneSmallSpectrum295.graph DegreeOneSmallSpectrum182.graph
    sourceMap0326 fusedMap0326 sourceMap0326_checked fusedMap0326_checked
    DegreeOneSmallComparisons.comparison0326
#print axioms sourceMap0326_checked
#print axioms fusedMap0326_checked
#print axioms certified0326
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
