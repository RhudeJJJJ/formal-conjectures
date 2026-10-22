/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0153 : Family 8 := level8.get ⟨161,by decide⟩
def sourceMap0153 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0153 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0153_checked : acceptsGraphIso
    (source (graph core0153) (root 8) 2 2) DegreeTwoThreeSpectrum3621.graph sourceMap0153=true := by decide +kernel
theorem fusedMap0153_checked : acceptsGraphIso
    (fused (graph core0153) (root 8) 2 2) DegreeTwoThreeSpectrum2819.graph fusedMap0153=true := by decide +kernel
theorem certified0153 : Certified (graph core0153) (root 8) 2 2 :=
  of_native_maps core0153 DegreeTwoThreeSpectrum3621.graph DegreeTwoThreeSpectrum2819.graph
    sourceMap0153 fusedMap0153 sourceMap0153_checked fusedMap0153_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0153
#print axioms sourceMap0153_checked
#print axioms fusedMap0153_checked
#print axioms certified0153
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
