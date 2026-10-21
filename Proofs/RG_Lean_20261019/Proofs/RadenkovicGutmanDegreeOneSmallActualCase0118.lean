/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0118 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0118 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![4,0,1,2,3,5,6,7,8] (sourceLabel 4 1 1 v)
def fusedMap0118 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap0118_checked : acceptsGraphIso
    (source (graph core0118) (root 4) 1 1) DegreeOneSmallSpectrum049.graph sourceMap0118=true := by decide +kernel
theorem fusedMap0118_checked : acceptsGraphIso
    (fused (graph core0118) (root 4) 1 1) DegreeOneSmallSpectrum034.graph fusedMap0118=true := by decide +kernel
theorem certified0118 : Certified (graph core0118) (root 4) 1 1 :=
  of_native_maps core0118 DegreeOneSmallSpectrum049.graph DegreeOneSmallSpectrum034.graph
    sourceMap0118 fusedMap0118 sourceMap0118_checked fusedMap0118_checked
    DegreeOneSmallComparisons.comparison0118
#print axioms sourceMap0118_checked
#print axioms fusedMap0118_checked
#print axioms certified0118
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
