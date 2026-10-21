/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0669 : Family 7 := level7.get ⟨62,by decide⟩
def sourceMap0669 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (sourceLabel 7 0 0 v)
def fusedMap0669 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0669_checked : acceptsGraphIso
    (source (graph core0669) (root 7) 0 0) SmallGeFourSpectrum028.graph sourceMap0669=true := by decide +kernel
theorem fusedMap0669_checked : acceptsGraphIso
    (fused (graph core0669) (root 7) 0 0) SmallGeFourSpectrum015.graph fusedMap0669=true := by decide +kernel
theorem certified0669 : Certified (graph core0669) (root 7) 0 0 :=
  of_native_maps core0669 SmallGeFourSpectrum028.graph SmallGeFourSpectrum015.graph
    sourceMap0669 fusedMap0669 sourceMap0669_checked fusedMap0669_checked
    DegreeOneSmallComparisons.comparison0669
#print axioms sourceMap0669_checked
#print axioms fusedMap0669_checked
#print axioms certified0669
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
