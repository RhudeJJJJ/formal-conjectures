/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0835 : Family 8 := level8.get ⟨30,by decide⟩
def sourceMap0835 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0835 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0835_checked : acceptsGraphIso
    (source (graph core0835) (root 8) 0 0) DegreeOneSmallSpectrum177.graph sourceMap0835=true := by decide +kernel
theorem fusedMap0835_checked : acceptsGraphIso
    (fused (graph core0835) (root 8) 0 0) DegreeOneSmallSpectrum225.graph fusedMap0835=true := by decide +kernel
theorem certified0835 : Certified (graph core0835) (root 8) 0 0 :=
  of_native_maps core0835 DegreeOneSmallSpectrum177.graph DegreeOneSmallSpectrum225.graph
    sourceMap0835 fusedMap0835 sourceMap0835_checked fusedMap0835_checked
    DegreeOneSmallComparisons.comparison0835
#print axioms sourceMap0835_checked
#print axioms fusedMap0835_checked
#print axioms certified0835
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
