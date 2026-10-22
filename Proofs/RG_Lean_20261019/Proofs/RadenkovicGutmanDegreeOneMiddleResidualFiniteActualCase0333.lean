/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0333 : Family 9 := level9.get ⟨202,by decide⟩
def sourceMap0333 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0333 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0333_checked : acceptsGraphIso
    (source (graph core0333) (root 9) 2 2) DegreeOneMiddleResidualSpectrum825.graph sourceMap0333=true := by decide +kernel
theorem fusedMap0333_checked : acceptsGraphIso
    (fused (graph core0333) (root 9) 2 2) DegreeTwoThreeSpectrum3984.graph fusedMap0333=true := by decide +kernel
theorem certified0333 : Certified (graph core0333) (root 9) 2 2 :=
  of_native_maps core0333 DegreeOneMiddleResidualSpectrum825.graph DegreeTwoThreeSpectrum3984.graph
    sourceMap0333 fusedMap0333 sourceMap0333_checked fusedMap0333_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0333
#print axioms sourceMap0333_checked
#print axioms fusedMap0333_checked
#print axioms certified0333
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
