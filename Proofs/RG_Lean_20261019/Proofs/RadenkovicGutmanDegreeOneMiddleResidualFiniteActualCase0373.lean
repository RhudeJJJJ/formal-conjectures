/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0373 : Family 9 := level9.get ⟨275,by decide⟩
def sourceMap0373 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0373 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0373_checked : acceptsGraphIso
    (source (graph core0373) (root 9) 2 2) DegreeOneMiddleResidualSpectrum893.graph sourceMap0373=true := by decide +kernel
theorem fusedMap0373_checked : acceptsGraphIso
    (fused (graph core0373) (root 9) 2 2) DegreeTwoThreeSpectrum4092.graph fusedMap0373=true := by decide +kernel
theorem certified0373 : Certified (graph core0373) (root 9) 2 2 :=
  of_native_maps core0373 DegreeOneMiddleResidualSpectrum893.graph DegreeTwoThreeSpectrum4092.graph
    sourceMap0373 fusedMap0373 sourceMap0373_checked fusedMap0373_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0373
#print axioms sourceMap0373_checked
#print axioms fusedMap0373_checked
#print axioms certified0373
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
