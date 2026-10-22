/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0009 : Family 7 := level7.get ⟨10,by decide⟩
def sourceMap0009 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap0009 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0009_checked : acceptsGraphIso
    (source (graph core0009) (root 7) 2 2) DegreeOneMiddleResidualSpectrum071.graph sourceMap0009=true := by decide +kernel
theorem fusedMap0009_checked : acceptsGraphIso
    (fused (graph core0009) (root 7) 2 2) DegreeTwoThreeSpectrum1712.graph fusedMap0009=true := by decide +kernel
theorem certified0009 : Certified (graph core0009) (root 7) 2 2 :=
  of_native_maps core0009 DegreeOneMiddleResidualSpectrum071.graph DegreeTwoThreeSpectrum1712.graph
    sourceMap0009 fusedMap0009 sourceMap0009_checked fusedMap0009_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0009
#print axioms sourceMap0009_checked
#print axioms fusedMap0009_checked
#print axioms certified0009
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
