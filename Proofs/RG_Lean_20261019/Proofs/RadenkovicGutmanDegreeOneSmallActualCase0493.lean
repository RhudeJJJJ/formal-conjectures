/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0493 : Family 7 := level7.get ⟨8,by decide⟩
def sourceMap0493 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0493 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0493_checked : acceptsGraphIso
    (source (graph core0493) (root 7) 1 1) DegreeOneSmallSpectrum450.graph sourceMap0493=true := by decide +kernel
theorem fusedMap0493_checked : acceptsGraphIso
    (fused (graph core0493) (root 7) 1 1) DegreeOneSmallSpectrum371.graph fusedMap0493=true := by decide +kernel
theorem certified0493 : Certified (graph core0493) (root 7) 1 1 :=
  of_native_maps core0493 DegreeOneSmallSpectrum450.graph DegreeOneSmallSpectrum371.graph
    sourceMap0493 fusedMap0493 sourceMap0493_checked fusedMap0493_checked
    DegreeOneSmallComparisons.comparison0493
#print axioms sourceMap0493_checked
#print axioms fusedMap0493_checked
#print axioms certified0493
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
