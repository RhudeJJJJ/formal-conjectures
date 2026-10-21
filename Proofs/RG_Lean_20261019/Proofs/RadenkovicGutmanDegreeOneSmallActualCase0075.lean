/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0075 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0075 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 1) → Fin 6 :=
  fun v => ![0,3,4,5,1,2] (sourceLabel 3 0 0 v)
def fusedMap0075 : (Vertices 3 ⊕ Fin 2) → Fin 6 :=
  fun v => ![0,1,2,3,4,5] (fusedLabel 3 0 0 v)
theorem sourceMap0075_checked : acceptsGraphIso
    (source (graph core0075) (root 3) 0 0) DegreeOneSmallSpectrum005.graph sourceMap0075=true := by decide +kernel
theorem fusedMap0075_checked : acceptsGraphIso
    (fused (graph core0075) (root 3) 0 0) DegreeOneSmallSpectrum006.graph fusedMap0075=true := by decide +kernel
theorem certified0075 : Certified (graph core0075) (root 3) 0 0 :=
  of_native_maps core0075 DegreeOneSmallSpectrum005.graph DegreeOneSmallSpectrum006.graph
    sourceMap0075 fusedMap0075 sourceMap0075_checked fusedMap0075_checked
    DegreeOneSmallComparisons.comparison0075
#print axioms sourceMap0075_checked
#print axioms fusedMap0075_checked
#print axioms certified0075
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
