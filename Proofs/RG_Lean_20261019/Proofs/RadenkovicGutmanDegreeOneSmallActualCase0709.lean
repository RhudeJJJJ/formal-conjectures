/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0709 : Family 7 := level7.get ⟨73,by decide⟩
def sourceMap0709 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0709 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0709_checked : acceptsGraphIso
    (source (graph core0709) (root 7) 1 1) DegreeOneSmallSpectrum715.graph sourceMap0709=true := by decide +kernel
theorem fusedMap0709_checked : acceptsGraphIso
    (fused (graph core0709) (root 7) 1 1) SmallGeFourSpectrum095.graph fusedMap0709=true := by decide +kernel
theorem certified0709 : Certified (graph core0709) (root 7) 1 1 :=
  of_native_maps core0709 DegreeOneSmallSpectrum715.graph SmallGeFourSpectrum095.graph
    sourceMap0709 fusedMap0709 sourceMap0709_checked fusedMap0709_checked
    DegreeOneSmallComparisons.comparison0709
#print axioms sourceMap0709_checked
#print axioms fusedMap0709_checked
#print axioms certified0709
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
