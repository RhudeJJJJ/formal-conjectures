/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0274 : Family 9 := level9.get ⟨100,by decide⟩
def sourceMap0274 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0274 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0274_checked : acceptsGraphIso
    (source (graph core0274) (root 9) 2 2) DegreeOneMiddleResidualSpectrum714.graph sourceMap0274=true := by decide +kernel
theorem fusedMap0274_checked : acceptsGraphIso
    (fused (graph core0274) (root 9) 2 2) DegreeTwoThreeSpectrum4086.graph fusedMap0274=true := by decide +kernel
theorem certified0274 : Certified (graph core0274) (root 9) 2 2 :=
  of_native_maps core0274 DegreeOneMiddleResidualSpectrum714.graph DegreeTwoThreeSpectrum4086.graph
    sourceMap0274 fusedMap0274 sourceMap0274_checked fusedMap0274_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0274
#print axioms sourceMap0274_checked
#print axioms fusedMap0274_checked
#print axioms certified0274
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
