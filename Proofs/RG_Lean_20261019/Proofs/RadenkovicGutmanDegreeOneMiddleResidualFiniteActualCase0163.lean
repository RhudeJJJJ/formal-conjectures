/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0163 : Family 8 := level8.get ⟨196,by decide⟩
def sourceMap0163 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0163 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0163_checked : acceptsGraphIso
    (source (graph core0163) (root 8) 2 2) DegreeOneMiddleResidualSpectrum347.graph sourceMap0163=true := by decide +kernel
theorem fusedMap0163_checked : acceptsGraphIso
    (fused (graph core0163) (root 8) 2 2) DegreeTwoThreeSpectrum2455.graph fusedMap0163=true := by decide +kernel
theorem certified0163 : Certified (graph core0163) (root 8) 2 2 :=
  of_native_maps core0163 DegreeOneMiddleResidualSpectrum347.graph DegreeTwoThreeSpectrum2455.graph
    sourceMap0163 fusedMap0163 sourceMap0163_checked fusedMap0163_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0163
#print axioms sourceMap0163_checked
#print axioms fusedMap0163_checked
#print axioms certified0163
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
