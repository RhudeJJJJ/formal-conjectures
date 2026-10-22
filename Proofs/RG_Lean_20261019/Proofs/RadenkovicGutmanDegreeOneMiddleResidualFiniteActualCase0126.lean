/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0126 : Family 8 := level8.get ⟨101,by decide⟩
def sourceMap0126 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0126 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0126_checked : acceptsGraphIso
    (source (graph core0126) (root 8) 2 2) DegreeOneMiddleResidualSpectrum270.graph sourceMap0126=true := by decide +kernel
theorem fusedMap0126_checked : acceptsGraphIso
    (fused (graph core0126) (root 8) 2 2) DegreeTwoThreeSpectrum2466.graph fusedMap0126=true := by decide +kernel
theorem certified0126 : Certified (graph core0126) (root 8) 2 2 :=
  of_native_maps core0126 DegreeOneMiddleResidualSpectrum270.graph DegreeTwoThreeSpectrum2466.graph
    sourceMap0126 fusedMap0126 sourceMap0126_checked fusedMap0126_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0126
#print axioms sourceMap0126_checked
#print axioms fusedMap0126_checked
#print axioms certified0126
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
