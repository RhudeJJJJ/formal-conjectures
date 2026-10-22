/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0301 : Family 9 := level9.get ⟨147,by decide⟩
def sourceMap0301 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0301 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0301_checked : acceptsGraphIso
    (source (graph core0301) (root 9) 2 2) DegreeOneMiddleResidualSpectrum763.graph sourceMap0301=true := by decide +kernel
theorem fusedMap0301_checked : acceptsGraphIso
    (fused (graph core0301) (root 9) 2 2) DegreeTwoThreeSpectrum3903.graph fusedMap0301=true := by decide +kernel
theorem certified0301 : Certified (graph core0301) (root 9) 2 2 :=
  of_native_maps core0301 DegreeOneMiddleResidualSpectrum763.graph DegreeTwoThreeSpectrum3903.graph
    sourceMap0301 fusedMap0301 sourceMap0301_checked fusedMap0301_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0301
#print axioms sourceMap0301_checked
#print axioms fusedMap0301_checked
#print axioms certified0301
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
