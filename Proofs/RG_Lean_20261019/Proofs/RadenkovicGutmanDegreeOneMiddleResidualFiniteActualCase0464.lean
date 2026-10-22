/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0464 : Family 9 := level9.get ⟨545,by decide⟩
def sourceMap0464 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0464 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0464_checked : acceptsGraphIso
    (source (graph core0464) (root 9) 2 2) DegreeOneMiddleResidualSpectrum908.graph sourceMap0464=true := by decide +kernel
theorem fusedMap0464_checked : acceptsGraphIso
    (fused (graph core0464) (root 9) 2 2) DegreeTwoThreeSpectrum4173.graph fusedMap0464=true := by decide +kernel
theorem certified0464 : Certified (graph core0464) (root 9) 2 2 :=
  of_native_maps core0464 DegreeOneMiddleResidualSpectrum908.graph DegreeTwoThreeSpectrum4173.graph
    sourceMap0464 fusedMap0464 sourceMap0464_checked fusedMap0464_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0464
#print axioms sourceMap0464_checked
#print axioms fusedMap0464_checked
#print axioms certified0464
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
