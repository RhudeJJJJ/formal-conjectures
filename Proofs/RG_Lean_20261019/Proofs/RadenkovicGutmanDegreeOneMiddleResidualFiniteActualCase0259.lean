/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0259 : Family 9 := level9.get ⟨79,by decide⟩
def sourceMap0259 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0259 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0259_checked : acceptsGraphIso
    (source (graph core0259) (root 9) 2 2) DegreeOneMiddleResidualSpectrum674.graph sourceMap0259=true := by decide +kernel
theorem fusedMap0259_checked : acceptsGraphIso
    (fused (graph core0259) (root 9) 2 2) DegreeTwoThreeSpectrum4023.graph fusedMap0259=true := by decide +kernel
theorem certified0259 : Certified (graph core0259) (root 9) 2 2 :=
  of_native_maps core0259 DegreeOneMiddleResidualSpectrum674.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap0259 fusedMap0259 sourceMap0259_checked fusedMap0259_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0259
#print axioms sourceMap0259_checked
#print axioms fusedMap0259_checked
#print axioms certified0259
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
