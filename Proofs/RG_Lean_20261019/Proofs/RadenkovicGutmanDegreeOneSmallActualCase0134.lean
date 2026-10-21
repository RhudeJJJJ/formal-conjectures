/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0134 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0134 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,5,6,7,8,1,2,3,4] (sourceLabel 4 1 1 v)
def fusedMap0134 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap0134_checked : acceptsGraphIso
    (source (graph core0134) (root 4) 1 1) DegreeOneSmallSpectrum054.graph sourceMap0134=true := by decide +kernel
theorem fusedMap0134_checked : acceptsGraphIso
    (fused (graph core0134) (root 4) 1 1) DegreeOneSmallSpectrum035.graph fusedMap0134=true := by decide +kernel
theorem certified0134 : Certified (graph core0134) (root 4) 1 1 :=
  of_native_maps core0134 DegreeOneSmallSpectrum054.graph DegreeOneSmallSpectrum035.graph
    sourceMap0134 fusedMap0134 sourceMap0134_checked fusedMap0134_checked
    DegreeOneSmallComparisons.comparison0134
#print axioms sourceMap0134_checked
#print axioms fusedMap0134_checked
#print axioms certified0134
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
