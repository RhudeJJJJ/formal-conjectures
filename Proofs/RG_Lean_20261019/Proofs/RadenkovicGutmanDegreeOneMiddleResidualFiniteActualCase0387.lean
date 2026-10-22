/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0387 : Family 9 := level9.get ⟨318,by decide⟩
def sourceMap0387 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0387 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0387_checked : acceptsGraphIso
    (source (graph core0387) (root 9) 2 2) DegreeOneMiddleResidualSpectrum738.graph sourceMap0387=true := by decide +kernel
theorem fusedMap0387_checked : acceptsGraphIso
    (fused (graph core0387) (root 9) 2 2) DegreeTwoThreeSpectrum4176.graph fusedMap0387=true := by decide +kernel
theorem certified0387 : Certified (graph core0387) (root 9) 2 2 :=
  of_native_maps core0387 DegreeOneMiddleResidualSpectrum738.graph DegreeTwoThreeSpectrum4176.graph
    sourceMap0387 fusedMap0387 sourceMap0387_checked fusedMap0387_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0387
#print axioms sourceMap0387_checked
#print axioms fusedMap0387_checked
#print axioms certified0387
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
