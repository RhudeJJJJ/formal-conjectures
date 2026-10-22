/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0003 : Family 7 := level7.get ⟨3,by decide⟩
def sourceMap0003 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0003 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0003_checked : acceptsGraphIso
    (source (graph core0003) (root 7) 2 2) DegreeOneMiddleResidualSpectrum048.graph sourceMap0003=true := by decide +kernel
theorem fusedMap0003_checked : acceptsGraphIso
    (fused (graph core0003) (root 7) 2 2) DegreeTwoThreeSpectrum1728.graph fusedMap0003=true := by decide +kernel
theorem certified0003 : Certified (graph core0003) (root 7) 2 2 :=
  of_native_maps core0003 DegreeOneMiddleResidualSpectrum048.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap0003 fusedMap0003 sourceMap0003_checked fusedMap0003_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0003
#print axioms sourceMap0003_checked
#print axioms fusedMap0003_checked
#print axioms certified0003
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
