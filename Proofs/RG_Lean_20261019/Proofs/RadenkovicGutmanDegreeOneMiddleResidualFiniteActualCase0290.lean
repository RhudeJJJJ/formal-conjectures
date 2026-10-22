/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0290 : Family 9 := level9.get ⟨126,by decide⟩
def sourceMap0290 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,8,9,10,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0290 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0290_checked : acceptsGraphIso
    (source (graph core0290) (root 9) 2 2) DegreeOneMiddleResidualSpectrum691.graph sourceMap0290=true := by decide +kernel
theorem fusedMap0290_checked : acceptsGraphIso
    (fused (graph core0290) (root 9) 2 2) DegreeTwoThreeSpectrum4157.graph fusedMap0290=true := by decide +kernel
theorem certified0290 : Certified (graph core0290) (root 9) 2 2 :=
  of_native_maps core0290 DegreeOneMiddleResidualSpectrum691.graph DegreeTwoThreeSpectrum4157.graph
    sourceMap0290 fusedMap0290 sourceMap0290_checked fusedMap0290_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0290
#print axioms sourceMap0290_checked
#print axioms fusedMap0290_checked
#print axioms certified0290
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
