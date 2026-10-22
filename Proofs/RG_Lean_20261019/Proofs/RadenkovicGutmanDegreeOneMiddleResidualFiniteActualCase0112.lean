/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0112 : Family 8 := level8.get ⟨73,by decide⟩
def sourceMap0112 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0112 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0112_checked : acceptsGraphIso
    (source (graph core0112) (root 8) 2 2) DegreeOneMiddleResidualSpectrum332.graph sourceMap0112=true := by decide +kernel
theorem fusedMap0112_checked : acceptsGraphIso
    (fused (graph core0112) (root 8) 2 2) DegreeTwoThreeSpectrum2384.graph fusedMap0112=true := by decide +kernel
theorem certified0112 : Certified (graph core0112) (root 8) 2 2 :=
  of_native_maps core0112 DegreeOneMiddleResidualSpectrum332.graph DegreeTwoThreeSpectrum2384.graph
    sourceMap0112 fusedMap0112 sourceMap0112_checked fusedMap0112_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0112
#print axioms sourceMap0112_checked
#print axioms fusedMap0112_checked
#print axioms certified0112
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
