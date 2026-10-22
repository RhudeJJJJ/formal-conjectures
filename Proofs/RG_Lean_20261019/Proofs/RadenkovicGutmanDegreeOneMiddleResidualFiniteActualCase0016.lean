/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0016 : Family 7 := level7.get ⟨19,by decide⟩
def sourceMap0016 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0016 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0016_checked : acceptsGraphIso
    (source (graph core0016) (root 7) 2 2) DegreeOneMiddleResidualSpectrum090.graph sourceMap0016=true := by decide +kernel
theorem fusedMap0016_checked : acceptsGraphIso
    (fused (graph core0016) (root 7) 2 2) DegreeTwoThreeSpectrum1725.graph fusedMap0016=true := by decide +kernel
theorem certified0016 : Certified (graph core0016) (root 7) 2 2 :=
  of_native_maps core0016 DegreeOneMiddleResidualSpectrum090.graph DegreeTwoThreeSpectrum1725.graph
    sourceMap0016 fusedMap0016 sourceMap0016_checked fusedMap0016_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0016
#print axioms sourceMap0016_checked
#print axioms fusedMap0016_checked
#print axioms certified0016
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
