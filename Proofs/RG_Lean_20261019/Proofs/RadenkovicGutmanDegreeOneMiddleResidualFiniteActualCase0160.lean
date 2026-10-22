/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0160 : Family 8 := level8.get ⟨189,by decide⟩
def sourceMap0160 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0160 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0160_checked : acceptsGraphIso
    (source (graph core0160) (root 8) 2 2) DegreeOneMiddleResidualSpectrum344.graph sourceMap0160=true := by decide +kernel
theorem fusedMap0160_checked : acceptsGraphIso
    (fused (graph core0160) (root 8) 2 2) DegreeTwoThreeSpectrum2437.graph fusedMap0160=true := by decide +kernel
theorem certified0160 : Certified (graph core0160) (root 8) 2 2 :=
  of_native_maps core0160 DegreeOneMiddleResidualSpectrum344.graph DegreeTwoThreeSpectrum2437.graph
    sourceMap0160 fusedMap0160 sourceMap0160_checked fusedMap0160_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0160
#print axioms sourceMap0160_checked
#print axioms fusedMap0160_checked
#print axioms certified0160
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
