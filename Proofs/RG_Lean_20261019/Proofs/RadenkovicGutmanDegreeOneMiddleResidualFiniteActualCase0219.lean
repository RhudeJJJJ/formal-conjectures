/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0219 : Family 9 := level9.get ⟨24,by decide⟩
def sourceMap0219 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0219 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0219_checked : acceptsGraphIso
    (source (graph core0219) (root 9) 2 2) DegreeOneMiddleResidualSpectrum715.graph sourceMap0219=true := by decide +kernel
theorem fusedMap0219_checked : acceptsGraphIso
    (fused (graph core0219) (root 9) 2 2) DegreeTwoThreeSpectrum3871.graph fusedMap0219=true := by decide +kernel
theorem certified0219 : Certified (graph core0219) (root 9) 2 2 :=
  of_native_maps core0219 DegreeOneMiddleResidualSpectrum715.graph DegreeTwoThreeSpectrum3871.graph
    sourceMap0219 fusedMap0219 sourceMap0219_checked fusedMap0219_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0219
#print axioms sourceMap0219_checked
#print axioms fusedMap0219_checked
#print axioms certified0219
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
