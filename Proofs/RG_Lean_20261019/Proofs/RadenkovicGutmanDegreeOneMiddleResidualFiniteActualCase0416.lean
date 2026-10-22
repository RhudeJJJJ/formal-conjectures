/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0416 : Family 9 := level9.get ⟨374,by decide⟩
def sourceMap0416 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0416 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0416_checked : acceptsGraphIso
    (source (graph core0416) (root 9) 2 2) DegreeOneMiddleResidualSpectrum787.graph sourceMap0416=true := by decide +kernel
theorem fusedMap0416_checked : acceptsGraphIso
    (fused (graph core0416) (root 9) 2 2) DegreeTwoThreeSpectrum4306.graph fusedMap0416=true := by decide +kernel
theorem certified0416 : Certified (graph core0416) (root 9) 2 2 :=
  of_native_maps core0416 DegreeOneMiddleResidualSpectrum787.graph DegreeTwoThreeSpectrum4306.graph
    sourceMap0416 fusedMap0416 sourceMap0416_checked fusedMap0416_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0416
#print axioms sourceMap0416_checked
#print axioms fusedMap0416_checked
#print axioms certified0416
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
