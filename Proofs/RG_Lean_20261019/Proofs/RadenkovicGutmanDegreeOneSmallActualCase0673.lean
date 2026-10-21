/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0673 : Family 7 := level7.get ⟨62,by decide⟩
def sourceMap0673 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0673 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0673_checked : acceptsGraphIso
    (source (graph core0673) (root 7) 1 1) SmallGeFourSpectrum125.graph sourceMap0673=true := by decide +kernel
theorem fusedMap0673_checked : acceptsGraphIso
    (fused (graph core0673) (root 7) 1 1) SmallGeFourSpectrum093.graph fusedMap0673=true := by decide +kernel
theorem certified0673 : Certified (graph core0673) (root 7) 1 1 :=
  of_native_maps core0673 SmallGeFourSpectrum125.graph SmallGeFourSpectrum093.graph
    sourceMap0673 fusedMap0673 sourceMap0673_checked fusedMap0673_checked
    DegreeOneSmallComparisons.comparison0673
#print axioms sourceMap0673_checked
#print axioms fusedMap0673_checked
#print axioms certified0673
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
