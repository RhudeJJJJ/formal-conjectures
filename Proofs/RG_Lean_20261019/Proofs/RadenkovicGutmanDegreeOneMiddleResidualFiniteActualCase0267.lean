/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0267 : Family 9 := level9.get ⟨89,by decide⟩
def sourceMap0267 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0267 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0267_checked : acceptsGraphIso
    (source (graph core0267) (root 9) 2 2) DegreeOneMiddleResidualSpectrum685.graph sourceMap0267=true := by decide +kernel
theorem fusedMap0267_checked : acceptsGraphIso
    (fused (graph core0267) (root 9) 2 2) DegreeTwoThreeSpectrum4052.graph fusedMap0267=true := by decide +kernel
theorem certified0267 : Certified (graph core0267) (root 9) 2 2 :=
  of_native_maps core0267 DegreeOneMiddleResidualSpectrum685.graph DegreeTwoThreeSpectrum4052.graph
    sourceMap0267 fusedMap0267 sourceMap0267_checked fusedMap0267_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0267
#print axioms sourceMap0267_checked
#print axioms fusedMap0267_checked
#print axioms certified0267
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
