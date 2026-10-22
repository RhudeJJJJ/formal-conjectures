/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0133 : Family 8 := level8.get ⟨113,by decide⟩
def sourceMap0133 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0133 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0133_checked : acceptsGraphIso
    (source (graph core0133) (root 8) 2 2) DegreeOneMiddleResidualSpectrum283.graph sourceMap0133=true := by decide +kernel
theorem fusedMap0133_checked : acceptsGraphIso
    (fused (graph core0133) (root 8) 2 2) DegreeTwoThreeSpectrum2525.graph fusedMap0133=true := by decide +kernel
theorem certified0133 : Certified (graph core0133) (root 8) 2 2 :=
  of_native_maps core0133 DegreeOneMiddleResidualSpectrum283.graph DegreeTwoThreeSpectrum2525.graph
    sourceMap0133 fusedMap0133 sourceMap0133_checked fusedMap0133_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0133
#print axioms sourceMap0133_checked
#print axioms fusedMap0133_checked
#print axioms certified0133
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
