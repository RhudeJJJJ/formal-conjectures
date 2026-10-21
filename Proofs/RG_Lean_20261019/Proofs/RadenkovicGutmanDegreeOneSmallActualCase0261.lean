/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0261 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0261 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 1 1 v)
def fusedMap0261 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0261_checked : acceptsGraphIso
    (source (graph core0261) (root 5) 1 1) DegreeOneSmallSpectrum155.graph sourceMap0261=true := by decide +kernel
theorem fusedMap0261_checked : acceptsGraphIso
    (fused (graph core0261) (root 5) 1 1) SmallGeFourSpectrum016.graph fusedMap0261=true := by decide +kernel
theorem certified0261 : Certified (graph core0261) (root 5) 1 1 :=
  of_native_maps core0261 DegreeOneSmallSpectrum155.graph SmallGeFourSpectrum016.graph
    sourceMap0261 fusedMap0261 sourceMap0261_checked fusedMap0261_checked
    DegreeOneSmallComparisons.comparison0261
#print axioms sourceMap0261_checked
#print axioms fusedMap0261_checked
#print axioms certified0261
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
